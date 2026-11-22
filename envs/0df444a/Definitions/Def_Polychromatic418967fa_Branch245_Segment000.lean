-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch245_Segment000
-- name    : Polychromatic418967fa_Branch245_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:25.7958+00:00
-- url     : https://prove2.me/theorems/a8ea7b9c-073e-4c9f-bd95-c4183447baf9
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

def Polychromatic418967fa.branch_245_segment_000 : allB 123 245 :=
  allB_succ 122 245 (allA_succ_of_accept 121 122 245 (accept_3_2 121 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 120 122 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 119 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 245 (accept_3_2 118 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 117 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 116 122 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 245 (accept_3_2 115 122 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 114 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 245
  (Polychromatic418967fa.accept_10_3_2_5_1_295 113 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 245 (accept_3_2 112 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 245 (Polychromatic418967fa.accept_13_6_5_11_1_1971 110 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 245 (accept_3_2 109 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 108 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 107 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 245 (accept_3_2 106 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 104 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 245 (accept_3_2 103 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 245
  (Polychromatic418967fa.accept_11_2_1_3_1_683 101 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 245 (accept_3_2 100 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 245 (accept_3_2 97 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 245 (accept_3_2 94 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 245 (accept_3_2 91 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 90 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 245 (accept_3_2 88 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076 86 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 245 (accept_3_2 85 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 245 (accept_3_2 82 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 245 (accept_3_2 79 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 245
  (Polychromatic418967fa.accept_10_7_2_5_1_298 77 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 245 (accept_3_2 76 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 245 (Polychromatic418967fa.accept_14_4_10_7_1_1946 74 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 245 (accept_3_2 73 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 245 (Polychromatic418967fa.accept_13_7_5_11_1_1927 72 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 245 (accept_3_2 70 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 68 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 245 (accept_3_2 67 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 245
  (Polychromatic418967fa.accept_21_2_17_14_1_5644 65 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 122 245 (accept_3_2 64 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 245 (accept_3_2 61 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421
  60 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 245 (accept_3_2 58 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 245 (accept_3_2 55 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 245 (Polychromatic418967fa.accept_19_16_8_17_1_5148 54 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 245 (accept_3_2 52 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 245 (Polychromatic418967fa.accept_17_16_3_7_1_5028 50 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 245 (accept_3_2 49 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 245 (accept_3_2 46 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 245 (accept_3_2 43 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 245
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 245 (accept_3_2 40 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 245 (accept_3_2 37 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 245 (Polychromatic418967fa.accept_21_15_17_14_1_4191 36
  122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 245 (accept_3_2 34 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 245 (accept_3_2 31 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 245
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 245 (accept_3_2 28 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 245 (accept_3_2 25 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 245 (accept_3_2 22 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 245 (accept_3_2 19 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 122
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 245 (accept_3_2 16 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 245 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 245 (accept_3_2 13 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 122 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 245 (accept_3_2 10 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 245 (accept_3_2 7 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 122 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 245
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 245 (accept_3_2 4 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 245 (accept_3_2 1 122 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 245 (allA_of_3_0 121 121 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 245
  (allA_succ_of_accept 119 120 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287 119 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 245 (accept_3_2 118 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 117 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 116 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 115 120 245 5 23 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 114 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 114 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 113 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 120 245 (accept_3_2 112 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 120 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 111 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 120 245 5 22 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 120 245 (accept_3_2 109 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 120 245 (Polychromatic418967fa.accept_16_12_8_5_1_3316 108 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417
  107 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 245 (accept_3_2
  106 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 120 245 5 21 24 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 120 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 104 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 245 (accept_3_2 103 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 245 (Polychromatic418967fa.accept_21_18_15_14_1_8871 102 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 101 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 245 5 20 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 245
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 99 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 120 245 (accept_3_2 97 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 120 245 5 19 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 120 245 (accept_3_2 94 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287 93 120
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 245
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 92 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 245 (accept_3_2 91 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  120 245 5 18 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 245 (accept_3_2 88 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171
  86 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 120 245 5 17 24 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 120 245
  (Polychromatic418967fa.accept_11_7_10_3_1_633 84 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 120 245 (Polychromatic418967fa.accept_13_5_3_11_1_1288 83 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 245 (accept_3_2 82 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 120 245 (Polychromatic418967fa.accept_18_9_12_11_1_5642 81 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 120 245 5 16 24 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 245 (accept_3_2 79 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431
  78 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 120 245 (accept_3_2 76 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  120 245 5 15 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 120 245 (Polychromatic418967fa.accept_26_22_16_11_1_14753 74 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 245 (accept_3_2 73 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 120 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 245 5 14 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 245 (accept_3_2 67
  120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 245
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 66 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 120 245 5 13 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 120 245 (accept_3_2 64 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 120 245 (Polychromatic418967fa.accept_18_9_12_11_1_5642 63 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417
  62 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 245 (accept_3_2 61
  120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 245 5 12 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 120 245 (accept_3_2 58 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 120 245 (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 120 245 (Polychromatic418967fa.accept_19_18_6_17_1_8078 56 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 120 245 5 11 24 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 120 245
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 245 (accept_3_2 52 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 245 5 10 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 245 (accept_3_2 49 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 245 (Polychromatic418967fa.accept_14_6_8_7_1_589 48 120
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 245
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 120 245 (accept_3_2 46 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  120 245 5 9 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 120 245 (accept_3_2 43 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 245 5 8 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 245
  (Polychromatic418967fa.accept_21_18_15_14_1_8871 39 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 245 (Polychromatic418967fa.accept_21_17_15_14_1_5707 38 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 245 (accept_3_2 37 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 120
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 120 245 5 7 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 245 (accept_3_2 34
  120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 245 (accept_3_2 31 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 120 245 5 6 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 120 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 245 (accept_3_2 28 120 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 245 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 120
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 120 245 5 5 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 245 (accept_3_2 22 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 245
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 245 5 4 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 245 (accept_3_2 19 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 245 (accept_3_2 16 120 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 245 5 3 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 245 (accept_3_2 13 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 245
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 245 (Polychromatic418967fa.accept_16_11_8_5_1_4366 11 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 245 5 2 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 245 (Polychromatic418967fa.accept_18_9_12_11_1_5642
  9 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 245 (accept_3_2 7 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 120 245 5 1 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 120 245 (accept_3_2 4 120 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 120 245 (Polychromatic418967fa.accept_16_3_8_5_1_6790 3 120 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 120
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 245 (accept_3_2 1 120 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 245 (allA_succ_of_accept 118 119 245 (accept_3_2 118 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 245 (Polychromatic418967fa.accept_19_3_5_17_1_9438 117 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 245
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 116 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 119 245 (accept_3_2 115 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 119 245 (Polychromatic418967fa.accept_13_9_2_11_1_1964 113 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 119 245 7 16 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 119 245
  (Polychromatic418967fa.accept_10_1_9_5_1_83 111 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 245 (accept_3_2 109 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 119 245 (Polychromatic418967fa.accept_13_4_2_11_1_733 108 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 245
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 107 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 119 245 (accept_3_2 106 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 119 245 7 15 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 119 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 104 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 245 (accept_3_2 103 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 245
  (Polychromatic418967fa.accept_10_1_9_5_1_83 101 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 119 245 (accept_3_2 100 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 119 245 (Polychromatic418967fa.accept_15_9_14_5_1_2086 99 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 119 245 7 14 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 119 245 (accept_3_2 97 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 119 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 96 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 245 (Polychromatic418967fa.accept_13_4_2_11_1_733 95 119
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 245 (accept_3_2 94 119
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 245
  (Polychromatic418967fa.accept_20_13_19_5_1_1012 93 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 92 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 119 245 7 13 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 119 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 119 245 (Polychromatic418967fa.accept_22_1_9_3_1_3674 89 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 245 (accept_3_2 88 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 119 245 (Polychromatic418967fa.accept_13_9_2_11_1_1964 87 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 245 (accept_3_2 85 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  119 245 7 12 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 119 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 83 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 245 (accept_3_2 82 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 119 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 245
  (Polychromatic418967fa.accept_23_11_4_15_1_11626 80 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 119 245 (accept_3_2 79 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 119 245 7 11 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 119 245 (accept_3_2 76 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 245 (Polychromatic418967fa.accept_13_10_2_11_1_1920 75 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 245 (accept_3_2 73 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 71 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 119 245 7 10 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 119 245
  (Polychromatic418967fa.accept_13_4_2_11_1_733 69 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 119 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999 68 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 245 (accept_3_2 67 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 245
  (Polychromatic418967fa.accept_23_19_4_15_1_14752 65 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 119 245 (accept_3_2 64 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 119 245 7 9 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 245 (accept_3_2 61 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 119 245 (Polychromatic418967fa.accept_16_12_7_5_1_1412 60 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 245
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 59 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 245 (accept_3_2 58 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 245 (Polychromatic418967fa.accept_23_11_4_15_1_11626 57 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 56 119 245 7 8 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 119 245 (accept_3_2 55 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 245
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 245 (accept_3_2 52 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 119 245 7 7 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 119 245
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 245 (accept_3_2 46 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 245 (Polychromatic418967fa.accept_19_7_5_17_1_3849 45 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 245
  (Polychromatic418967fa.accept_10_4_9_5_1_84 44 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 245 (accept_3_2 43 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  119 245 7 6 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 119 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 245 (accept_3_2 40 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 245 (accept_3_2 37 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  36 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 119 245 7 5 17 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 119 245
  (accept_3_2 34 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 245
  (Polychromatic418967fa.accept_19_14_5_17_1_6542 33 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 245 (accept_3_2 31 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 245
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 245 7 4 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 245 (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 245 (accept_3_2 25 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 245 (Polychromatic418967fa.accept_10_4_9_5_1_84
  24 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 245
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 119 245 (accept_3_2 22 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 119 245 7 3 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 119 245 (Polychromatic418967fa.accept_22_20_9_3_1_14751 20 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 245 (accept_3_2 19 119 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 245
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 245 (accept_3_2 16 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 245 (Polychromatic418967fa.accept_19_15_5_17_1_8036 15 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 119 245 7 2 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 119 245 (accept_3_2 13 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 245 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 245 (accept_3_2 10 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 245 (Polychromatic418967fa.accept_13_9_2_11_1_1964
  9 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 245
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 119 245 7 1 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 119 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 245 (Polychromatic418967fa.accept_22_5_9_3_1_5251 5 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 245 (accept_3_2 4 119 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999
  3 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 245 (accept_3_2 1 119 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 245 (allA_of_3_0 118 118 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 245
  (allA_succ_of_accept 116 117 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 245 (accept_3_2 115 117 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 114 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 245
  (Polychromatic418967fa.accept_10_3_7_5_1_288 113 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 245 (accept_3_2 112 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 111 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 245 (accept_3_2 109 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 108 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 245
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 107 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 245 (accept_3_2 106 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 245 (Polychromatic418967fa.accept_18_15_9_11_1_4371 105 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 245 (accept_3_2 103 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 102 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 245
  (Polychromatic418967fa.accept_19_6_3_17_1_9472 101 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 245 (accept_3_2 100 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 117 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 245 (accept_3_2 97 117 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 245
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 96 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 245 (Polychromatic418967fa.accept_20_15_17_5_1_6040 95 117 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 245 (accept_3_2 94 117 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 245 (accept_3_2 91 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 245 (Polychromatic418967fa.accept_17_5_15_7_1_4992 90 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 245 (Polychromatic418967fa.accept_21_5_12_14_1_7241 89 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 245 (accept_3_2 88 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 87 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 245 (accept_3_2 85 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 83 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 245 (accept_3_2 82 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 245 (accept_3_2 79 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 78 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 77 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 245 (accept_3_2 76 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 245 (accept_3_2 73 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 245 (Polychromatic418967fa.accept_19_14_3_17_1_6558 71 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 245 (accept_3_2 70 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 245 (accept_3_2 67 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 65 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 245 (accept_3_2 64 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 245 (accept_3_2 61 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 245 (Polychromatic418967fa.accept_17_9_15_7_1_6212 60 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 245 (accept_3_2 58 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 245 (Polychromatic418967fa.accept_21_15_12_14_1_7232 57
  117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 245 (accept_3_2 55 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 245 (accept_3_2 52 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 245 (accept_3_2 49 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 245 (accept_3_2 46 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 245 (Polychromatic418967fa.accept_21_3_12_14_1_8848 45 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 245 (accept_3_2 43 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 245 (Polychromatic418967fa.accept_22_19_7_3_1_11746 41 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 245 (accept_3_2 40 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 245 (accept_3_2 37 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 245 (Polychromatic418967fa.accept_19_16_3_17_1_6575 35 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 245 (accept_3_2 34 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 245 (accept_3_2 31 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 245 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 245 (Polychromatic418967fa.accept_21_8_12_14_1_10464 29 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 245 (accept_3_2 28 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 245 (accept_3_2 25 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 245 (accept_3_2 22 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 245 (accept_3_2 19 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 245 (accept_3_2 16 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 117
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 245 (accept_3_2 13 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 245 (Polychromatic418967fa.accept_20_11_17_5_1_13413 11 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 245 (accept_3_2 10 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 245 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 117 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 245 (accept_3_2 7 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 245 (Polychromatic418967fa.accept_17_5_15_7_1_4992 5 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 245 (accept_3_2 4 117 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 245 (accept_3_2 1 117 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 245 (allA_succ_of_accept 115 116 245 (accept_3_2 115 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 114 116 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 113 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 245 (accept_3_2 112 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 110 116 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 245 (accept_3_2 109 116 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 108 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 245
  (Polychromatic418967fa.accept_11_8_6_3_1_661 107 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 245 (accept_3_2 106 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 245 (accept_3_2 103 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 102 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 245
  (Polychromatic418967fa.accept_10_1_6_5_1_304 101 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 245 (accept_3_2 100 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 245 (accept_3_2 97 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 245 (accept_3_2 94 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 92 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 245 (accept_3_2 91 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 245 (Polychromatic418967fa.accept_19_14_2_17_1_678 90 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 89 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 245 (accept_3_2 88 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 245 (accept_3_2 85 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 245
  (Polychromatic418967fa.accept_15_8_11_5_1_169 83 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 245 (accept_3_2 82 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 245 (Polychromatic418967fa.accept_14_10_4_7_1_1214 80 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 245 (accept_3_2 79 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 245 (accept_3_2 76 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 74 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 245 (accept_3_2 73 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 245 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 245
  (Polychromatic418967fa.accept_10_1_6_5_1_304 71 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 245 (accept_3_2 70 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 245 (accept_3_2 67 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 245 (accept_3_2 64 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 245 (accept_3_2 61 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 245 (accept_3_2 58 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 245 (Polychromatic418967fa.accept_13_4_12_11_1_5362 56 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 245 (accept_3_2 55 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 245
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 245 (accept_3_2 52 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 245 (accept_3_2 49 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 245
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 245 (accept_3_2 46 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 245 (accept_3_2 43 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 245 (accept_3_2 40 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 245 (accept_3_2 37 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 245 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 245
  (Polychromatic418967fa.accept_19_16_2_17_1_8049 35 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 116 245 (accept_3_2 34 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 245 (accept_3_2 31 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162
  30 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 245
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 245 (accept_3_2 28 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 245 (accept_3_2 25 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 116 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 245 (accept_3_2 22 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 245 (accept_3_2 19 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 245 (Polychromatic418967fa.accept_20_18_16_5_1_9137 18 116
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 245 (accept_3_2 16 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 245 (accept_3_2 13 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 245
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 245 (accept_3_2 10 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 245 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 245 (accept_3_2 7 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 116 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 245 (accept_3_2 4 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 245 (accept_3_2 1 116 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 245 (allA_of_3_0 115 115 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 245
  (allA_succ_of_accept 113 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 113 114 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 245 (accept_3_2 112 114 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 245
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 110 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 114 245 (accept_3_2 109 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 245 (Polychromatic418967fa.accept_13_4_10_11_1_1908 108 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50
  107 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 245 (accept_3_2
  106 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 245
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 105 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 114 245 (accept_3_2 103 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 114
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 245
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 101 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 114 245 (accept_3_2 100 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 245 (accept_3_2 97 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 96 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 114 245 (accept_3_2 94 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 114 245 (Polychromatic418967fa.accept_13_1_10_11_1_1280 92 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 245 (accept_3_2 91 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 90
  114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 114 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 114 245 (accept_3_2 88 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 245 (accept_3_2 85 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 114 245 (accept_3_2 82 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 114 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 245 (accept_3_2 79 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 245 (Polychromatic418967fa.accept_15_3_9_5_1_2082 78 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 114 245 (accept_3_2 76 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 114 245 (Polychromatic418967fa.accept_15_14_9_5_1_3932 74 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 245 (accept_3_2 73 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 114
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 245 (accept_3_2 70 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 114 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 245 (accept_3_2 67 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 245
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 65 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 245 (accept_3_2 64 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 245 (accept_3_2 61 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 245 (Polychromatic418967fa.accept_13_8_10_11_1_2730 60 114 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 245 (accept_3_2 58 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 114 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 245 (accept_3_2 55 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 114
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 245 (accept_3_2 52 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 245 (accept_3_2 49 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 245 (accept_3_2 46 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 245 (Polychromatic418967fa.accept_16_13_2_5_1_3336 45 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 245 (accept_3_2 43 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 42 114 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 245 (accept_3_2 40 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 38 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 245 (accept_3_2 37 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 114
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 245 (accept_3_2 34 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 245 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 245 (accept_3_2 31 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 245
  (Polychromatic418967fa.accept_10_9_4_5_1_616 29 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 245 (accept_3_2 28 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 245 (accept_3_2 25 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 245 (Polychromatic418967fa.accept_21_3_9_14_1_5701 24 114 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 245 (accept_3_2 22 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 245 (Polychromatic418967fa.accept_17_3_12_7_1_4949 20 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 245 (accept_3_2 19 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 114
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 245 (accept_3_2 16 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 245 (accept_3_2 13 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 245 (accept_3_2 10 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 245 (accept_3_2 7 114 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 245 (accept_3_2 4 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 245 (accept_3_2 1 114 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 245 (allA_succ_of_accept 112 113 245 (accept_3_2 112 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 113 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 245 (Polychromatic418967fa.accept_20_10_13_5_1_6086 110
  113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 245 (accept_3_2 109
  113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 108 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 113 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 245 (accept_3_2 106 113 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 105 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 245
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 104 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 245 (accept_3_2 103 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 101 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 245 (accept_3_2 100 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 245 (Polychromatic418967fa.accept_13_8_9_11_1_1265 99 113
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 98 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 245 (accept_3_2 97 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 245 (Polychromatic418967fa.accept_16_15_1_5_1_2265 95 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 245 (accept_3_2 94 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 92 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 245 (accept_3_2 91 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 245 (Polychromatic418967fa.accept_14_6_1_7_1_2775 90 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 245 (accept_3_2 88 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 245
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 86 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 245 (accept_3_2 85 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 245 (Polychromatic418967fa.accept_14_13_1_7_1_1211 83 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 245 (accept_3_2 82 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 245 (Polychromatic418967fa.accept_17_13_11_7_1_4961 81 113
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 245 (accept_3_2 79 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 245 (accept_3_2 76 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 245
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 74 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 245 (accept_3_2 73 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 245 (accept_3_2 70 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 68 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 245 (accept_3_2 67 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 245 (Polychromatic418967fa.accept_21_2_8_14_1_4148 65 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 245 (accept_3_2 64 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 245 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 113
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 245 (accept_3_2 61 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 245 (Polychromatic418967fa.accept_13_7_9_11_1_705 59 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 245 (accept_3_2 58 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 245
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 245 (accept_3_2 55 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 245 (Polychromatic418967fa.accept_13_2_9_11_1_258 54 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 245 (accept_3_2 52 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 245
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 50 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 245 (accept_3_2 49 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 245 (accept_3_2 46 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 245 (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 113
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 245 (accept_3_2 43 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 245 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 245 (accept_3_2 40 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 245
  (Polychromatic418967fa.accept_10_8_3_5_1_613 38 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 245 (accept_3_2 37 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 245 (accept_3_2 34 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 245
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 245 (accept_3_2 31 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 245 (accept_3_2 28 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 113
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 245 (accept_3_2 25 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 245 (Polychromatic418967fa.accept_19_4_18_17_1_1511 23 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 245 (accept_3_2 22 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 245 (accept_3_2 19 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 245 (accept_3_2 16 113 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 245
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 245 (accept_3_2 13 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 245 (accept_3_2 10 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 245 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 245 (accept_3_2 7 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 245 (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 245 (accept_3_2 4 113 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 113 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 245
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 245 (accept_3_2 1 113 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 245 (allA_of_3_0 112 112 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 245
  (allA_succ_of_accept 110 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 245 (accept_3_2 109 111 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 245 (Polychromatic418967fa.accept_13_4_7_11_1_1981 108 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 107 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 245 (accept_3_2 106 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 245 (accept_3_2 103 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 245
  (Polychromatic418967fa.accept_11_2_1_3_1_683 101 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 245 (accept_3_2 100 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 99 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 245 (accept_3_2 97 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 245 (accept_3_2 94 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 245 (accept_3_2 91 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 89 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 245 (accept_3_2 88 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 245 (accept_3_2 85 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 245
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 83 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 245 (accept_3_2 82 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 245 (accept_3_2 79 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 245 (accept_3_2 76 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 245 (Polychromatic418967fa.accept_19_18_16_17_1_2626 75 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 245 (accept_3_2 73 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 245 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 111
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 245 (accept_3_2 70 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 245 (accept_3_2 67 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 245
  (Polychromatic418967fa.accept_16_1_15_5_1_708 65 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 245 (accept_3_2 64 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 245 (accept_3_2 61 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 245 (accept_3_2 58 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 57 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 245 (accept_3_2 55 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 245 (accept_3_2 52 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 245 (accept_3_2 49 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 245 (Polychromatic418967fa.accept_13_9_7_11_1_1292 48 111 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 245
  (Polychromatic418967fa.accept_23_1_19_15_1_11644 47 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 111 245 (accept_3_2 46 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 111 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 245 (accept_3_2 43 111 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 245 (accept_3_2 40 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 245 (accept_3_2 37 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 245 (accept_3_2 34 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 245 (accept_3_2 31 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 245
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 245 (accept_3_2 28 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 245 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 245 (accept_3_2 25 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 245 (accept_3_2 22 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 245 (accept_3_2 19 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 245 (accept_3_2 16 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 245 (accept_3_2 13 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 245 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 111 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 245
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 245 (accept_3_2 10 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 245 (accept_3_2 7 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 245 (accept_3_2 4 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 245 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 111 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 245 (accept_3_2 1 111 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 245 (allA_succ_of_accept 109 110 245 (accept_3_2 109 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 245 (Polychromatic418967fa.accept_13_4_6_11_1_2017 108 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50
  107 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 245 (accept_3_2
  106 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 110 245 5 21 22 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 110 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 104 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 110 245 (accept_3_2 103 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 110 245 (Polychromatic418967fa.accept_19_7_15_17_1_5198 102 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 245 (Polychromatic418967fa.accept_17_16_8_7_1_4983 101 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 245 5 20 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 110 245 (Polychromatic418967fa.accept_19_3_15_17_1_12070 98 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 245 (accept_3_2 97 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 245 (Polychromatic418967fa.accept_13_5_6_11_1_1933 96 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 110 245 5 19 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 110 245 (accept_3_2 94
  110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 110 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 245 (accept_3_2 91 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 110 245 5 18 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 110 245 (Polychromatic418967fa.accept_14_5_12_7_1_2767 89 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 110 245 (accept_3_2 88 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 110 245
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 86 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 110 245 5 17 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 110 245 (Polychromatic418967fa.accept_17_16_8_7_1_4983 84 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 245 (accept_3_2 82 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 110 245 5 16 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 110 245 (accept_3_2 79 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 110 245 (Polychromatic418967fa.accept_19_2_15_17_1_2614 78 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 245
  (Polychromatic418967fa.accept_19_1_15_17_1_701 77 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 245 (accept_3_2 76 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  110 245 5 15 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 110 245 (Polychromatic418967fa.accept_16_10_14_5_1_5496 74 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 245 (accept_3_2 73 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 245 (Polychromatic418967fa.accept_14_2_12_7_1_617 72 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 245 5 14 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  68 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 245 (accept_3_2 67
  110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 245
  (Polychromatic418967fa.accept_20_6_10_5_1_10630 66 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 110 245 5 13 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 110 245 (accept_3_2 64 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 245 (Polychromatic418967fa.accept_19_5_15_17_1_9432 62 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 245 (accept_3_2 61 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 110 245 5 12 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 110 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 245 (accept_3_2 58 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 110 245 5 11 22 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 110 245
  (Polychromatic418967fa.accept_20_14_10_5_1_2117 54 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 245 (Polychromatic418967fa.accept_18_17_2_11_1_9749 53 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 245 (accept_3_2 52 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 245 5 10 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 245 (accept_3_2 49
  110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 245
  (Polychromatic418967fa.accept_17_14_8_7_1_6183 48 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 245 (accept_3_2 46 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 110 245 5 9 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 245 (accept_3_2 43 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 245 (Polychromatic418967fa.accept_16_10_14_5_1_5496 42 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 245
  (Polychromatic418967fa.accept_16_9_14_5_1_2239 41 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 245 5 8 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 245 (Polychromatic418967fa.accept_17_4_8_7_1_7469 38 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 245 (accept_3_2 37 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 245
  (Polychromatic418967fa.accept_20_16_10_5_1_9133 36 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 110 245 5 7 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 110 245 (accept_3_2 34 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 245 (accept_3_2 31 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 110 245 5 6 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 110 245
  (Polychromatic418967fa.accept_19_10_15_17_1_6590 29 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 110 245 (accept_3_2 28 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 245 (Polychromatic418967fa.accept_16_10_14_5_1_5496 26 110
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 110 245 5 5 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 245
  (Polychromatic418967fa.accept_19_5_15_17_1_9432 24 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 245 (accept_3_2 22 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 245 5 4 22 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 245 (accept_3_2 19 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 245
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 245 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 245 (accept_3_2 16 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 110 245 5 3 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 110 245 (Polychromatic418967fa.accept_17_14_8_7_1_6183 14 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 245 (accept_3_2 13 110 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 245 (Polychromatic418967fa.accept_19_12_15_17_1_3837 12
  110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 245 5 2 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 245 (accept_3_2 7 110 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 245
  (Polychromatic418967fa.accept_20_6_10_5_1_10630 6 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 110 245 5 1 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 110 245 (accept_3_2 4 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 245 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 245 (accept_3_2 1 110 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 245 (allA_of_3_0 109 109 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 245
  (allA_succ_of_accept 107 108 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 107 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 245 (accept_3_2 106 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 105 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 245
  (Polychromatic418967fa.accept_16_8_12_5_1_200 104 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 245 (accept_3_2 103 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 102 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 108 245 (Polychromatic418967fa.accept_13_10_4_11_1_1969 101 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 245 (accept_3_2 100 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 99 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 245
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 98 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 245 (accept_3_2 97 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 96 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 245 (Polychromatic418967fa.accept_14_11_10_7_1_1948 95 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 245 (accept_3_2 94 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 93 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 92 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 245 (accept_3_2 91 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 245 (Polychromatic418967fa.accept_13_12_4_11_1_1925 90 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 89 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 245 (accept_3_2 88 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 87 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 245
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 86 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 245 (accept_3_2 85 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 108 245 (Polychromatic418967fa.accept_13_6_4_11_1_282 84 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 83 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 245 (accept_3_2 82 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 108 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 245
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 80 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 245 (accept_3_2 79 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 245 (Polychromatic418967fa.accept_21_15_3_14_1_4141 78 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 245 (accept_3_2 76 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 245 (Polychromatic418967fa.accept_13_10_4_11_1_1969 75 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 245
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 74 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 245 (accept_3_2 73 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 108 245 (Polychromatic418967fa.accept_13_6_4_11_1_282 71 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 245 (accept_3_2 70 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 245
  (Polychromatic418967fa.accept_15_8_3_5_1_608 68 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 245 (accept_3_2 67 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 66 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 245 (accept_3_2 64 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 245 (accept_3_2 61 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 245 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 245 (accept_3_2 58 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 108 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 245
  (Polychromatic418967fa.accept_16_8_12_5_1_200 56 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 245 (accept_3_2 55 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 245 (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 53 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 245 (accept_3_2 52 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 245 (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 245
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 245 (accept_3_2 49 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 245 (Polychromatic418967fa.accept_17_14_6_7_1_4980 48 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 245 (accept_3_2 46 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 245 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 245
  (Polychromatic418967fa.accept_19_6_13_17_1_8015 44 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 108 245 (accept_3_2 43 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 108 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 245 (accept_3_2 40 108 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103
  39 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 245
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 38 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 245 (accept_3_2 37 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 245 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 245
  (Polychromatic418967fa.accept_19_16_13_17_1_12066 35 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 108 245 (accept_3_2 34 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 245 (accept_3_2 31 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 245
  (Polychromatic418967fa.accept_17_13_6_7_1_4999 30 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 245 (Polychromatic418967fa.accept_21_8_3_14_1_4165 29 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 245 (accept_3_2 28 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 245
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 26 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 108 245 (accept_3_2 25 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 245 (accept_3_2 22 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 245
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 245 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 245 (accept_3_2 19 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 245 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 245 (accept_3_2 16 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 245 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 245 (Polychromatic418967fa.accept_17_14_6_7_1_4980 14 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 245 (accept_3_2 13 108 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 245
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 108 245 (accept_3_2 10 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 108 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 108
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 245 (accept_3_2 7 108 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103
  6 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 245
  (Polychromatic418967fa.accept_22_5_20_3_1_13286 5 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 245 (accept_3_2 4 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 245 (accept_3_2 1 108 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 245 (allA_succ_of_accept 106 107 245 (accept_3_2 106 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 105 107 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 245 (accept_3_2 103 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 101 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 245 (accept_3_2 100 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 245 (Polychromatic418967fa.accept_13_8_3_11_1_3467 99 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 245 (accept_3_2 97 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 245 (accept_3_2 94 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 93 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 245
  (Polychromatic418967fa.accept_10_2_7_5_1_605 92 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 245 (accept_3_2 91 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 89 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 245 (accept_3_2 88 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 245 (accept_3_2 85 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 83 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 245 (accept_3_2 82 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 245 (Polychromatic418967fa.accept_19_5_12_17_1_8089 81 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 245
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 80 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 245 (accept_3_2 79 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 245 (accept_3_2 76 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 245 (accept_3_2 73 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 245 (accept_3_2 70 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 245 (accept_3_2 67 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 245 (Polychromatic418967fa.accept_24_17_11_5_1_7987 65 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 245 (accept_3_2 64 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 245 (accept_3_2 61 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 245 (accept_3_2 58 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 245
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 245 (accept_3_2 55 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 245 (accept_3_2 52 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 245 (accept_3_2 49 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 245 (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 245 (accept_3_2 46 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 245 (Polychromatic418967fa.accept_17_11_5_7_1_6177 45 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 245
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 245 (accept_3_2 43 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 245 (accept_3_2 40 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 245 (accept_3_2 37 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 245 (Polychromatic418967fa.accept_20_15_7_5_1_2115 35 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 245 (accept_3_2 34 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 245 (accept_3_2 31 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 245 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 245 (accept_3_2 28 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 245 (accept_3_2 25 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 245 (accept_3_2 22 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 245
  (Polychromatic418967fa.accept_13_7_3_11_1_280 20 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 245 (accept_3_2 19 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 245 (accept_3_2 16 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 245 (accept_3_2 13 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 245 (accept_3_2 10 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 245 (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 107
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 245
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 245 (accept_3_2 7 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 245 (accept_3_2 4 107 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 107 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 245 (accept_3_2 1 107 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 245 (allA_of_3_0 106 106 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 245
  (allA_succ_of_accept 104 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 245 (accept_3_2 103 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 245
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 101 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 105 245 5 20 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 105 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 105 245 7 14 15 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 105 245 (accept_3_2 97 105 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 245 (Polychromatic418967fa.accept_11_8_6_3_1_661
  96 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 105 245 5 19 21 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 105 245
  (accept_3_2 94 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 105 245 7 13 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 105 245 5 18 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 105 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 245 (accept_3_2 88 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 245 5 17 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 105 245 7 12 15 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 245
  (Polychromatic418967fa.accept_19_7_10_17_1_8088 83 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 105 245 (accept_3_2 82 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 105 245 (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 105 245 5 16 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 245 (accept_3_2 79 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 245 (Polychromatic418967fa.accept_16_14_9_5_1_4388 78 105 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 245 7 11 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 245 (accept_3_2 76
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 245 5 15 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 245 (accept_3_2 73 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 105 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 72 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 245 35 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 245
  (Polychromatic418967fa.accept_19_12_10_17_1_5189 69 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 245 (accept_3_2 67 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 245 5 13 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 245 (accept_3_2 64 105 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 245 7 9 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 245 (accept_3_2 61 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  105 245 5 12 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 105 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 245 (accept_3_2 58 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 105 245 7 8 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 105 245 5 11 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 245
  (Polychromatic418967fa.accept_22_10_17_3_1_14750 54 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 245 (accept_3_2 52 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 245 5 10 21 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 105 245 7 7 15 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 105 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 245 (Polychromatic418967fa.accept_13_8_1_11_1_1284 47 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 245 (accept_3_2 46 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 105 245 5 9 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 245 (accept_3_2 43 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 245 7 6 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 41
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 245 5 8 21 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 245 (accept_3_2 37 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 245 35 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 245 (accept_3_2 34 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 245 (accept_3_2 31 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  105 245 5 6 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 105 245 (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 105 245 7 4 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 105 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 105 245 5 5 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 105 245 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 245 (Polychromatic418967fa.accept_9_5_6_2_1_161
  23 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 245 (accept_3_2 22
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 245 7 3 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 245 5 4 21 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 245 (accept_3_2 19 105 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 245 (Polychromatic418967fa.accept_19_18_10_17_1_5192 18
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 245 (accept_3_2 16 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  105 245 5 3 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14
  105 245 7 2 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 105 245 (accept_3_2 13 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 245
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 245 (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 245 5 2 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 245 7 1 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 245 (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 245 5 1 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 245 (accept_3_2 4 105 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2
  105 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 245 (accept_3_2 1 105
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 245 (allA_succ_of_accept 103 104 245 (accept_3_2 103 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 104 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 101 104
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 245 (accept_3_2 100 104
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 104 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 245 (accept_3_2 97 104 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 245
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 95 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 104 245 (accept_3_2 94 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 104 245 (Polychromatic418967fa.accept_14_8_6_7_1_1934 92 104
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 245 (accept_3_2 91 104
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 245
  (Polychromatic418967fa.accept_19_14_9_17_1_14749 90 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 104 245 (accept_3_2 88 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 104 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 86 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 104 245 (accept_3_2 85 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 104 245 (Polychromatic418967fa.accept_14_13_6_7_1_2013 83 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 104 245 (accept_3_2 82 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 104 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 104 245 (accept_3_2 79 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 104 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 104 245 (accept_3_2 76 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 245
  (Polychromatic418967fa.accept_11_8_5_3_1_694 74 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 245 (accept_3_2 73 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 245 (Polychromatic418967fa.accept_21_9_20_14_1_4139 72 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 245 (accept_3_2 70 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 245
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 68 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 245 (accept_3_2 67 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 245 (Polychromatic418967fa.accept_19_8_9_17_1_5151 65 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 245 (accept_3_2 64 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 245 (accept_3_2 61 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 59 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 245 (accept_3_2 58 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 245 (accept_3_2 55 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 245 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 245 (accept_3_2 52 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 245 (accept_3_2 49 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 245 (accept_3_2 46 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 245 (accept_3_2 43 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 245 (accept_3_2 40 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 245 (accept_3_2 37 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 245 (accept_3_2 34 104 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 245
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 245 (accept_3_2 31 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 245 (accept_3_2 28 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 245 (accept_3_2 25 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 245 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 245 (accept_3_2 22 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 245
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 245 (accept_3_2 19 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 245 (Polychromatic418967fa.accept_21_18_20_14_1_5711 18 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 245 (accept_3_2 16 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 245 (accept_3_2 13 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 245 (accept_3_2 10 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 245 (accept_3_2 7 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 245 (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 245 (accept_3_2 4 104 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 245 (accept_3_2 1 104 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 245 (allA_of_3_0 103 103 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 245 (allA_succ_of_accept 101
  102 245 (Polychromatic418967fa.accept_14_3_4_7_1_175 101 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 245 (accept_3_2 100 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 245 (accept_3_2 97 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431
  96 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 245 (accept_3_2 94 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 93 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 92 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 245 (accept_3_2 91 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 245 (Polychromatic418967fa.accept_20_10_2_5_1_10647 90 102
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 89 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 245 (accept_3_2 88 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 245 (accept_3_2 85 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 84 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 245 (accept_3_2 82 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 102 245 (Polychromatic418967fa.accept_14_11_4_7_1_609 81 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 245 (accept_3_2 79 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 245 (accept_3_2 76 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 102 245 (Polychromatic418967fa.accept_21_11_18_14_1_5646 74 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 245 (accept_3_2 73 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 245 (Polychromatic418967fa.accept_19_15_7_17_1_5168 72 102
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 245 (accept_3_2 70 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 102 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 245 (accept_3_2 67 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 245 (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 245
  (Polychromatic418967fa.accept_16_1_6_5_1_4385 65 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 245 (accept_3_2 64 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 245 (accept_3_2 61 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 245 (accept_3_2 58 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 102 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 102 245 (Polychromatic418967fa.accept_19_18_7_17_1_6544 56 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 245 (accept_3_2 55 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 54 102
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 245 (accept_3_2 52 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 102 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 245 (accept_3_2 49 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 245 (accept_3_2 46 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 245 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 245 (accept_3_2 43 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 245 (accept_3_2 40 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 245 (accept_3_2 37 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 102
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 245 (accept_3_2 34 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 245 (accept_3_2 31 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 245 (Polychromatic418967fa.accept_20_10_2_5_1_10647 30 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 245
  (Polychromatic418967fa.accept_19_10_7_17_1_9496 29 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 102 245 (accept_3_2 28 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 245 (accept_3_2 25 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431
  24 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 245 (accept_3_2 22 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 245 (Polychromatic418967fa.accept_16_4_6_5_1_2245 20 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 245 (accept_3_2 19 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 245 (accept_3_2 16 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 245 (accept_3_2 13 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 245 (Polychromatic418967fa.accept_21_12_18_14_1_8854 12 102 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 245 (accept_3_2 10 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 245 (accept_3_2 7 102 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 245 (accept_3_2 4 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 245 (accept_3_2 1 102 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 245 (allA_succ_of_accept 100 101 245 (accept_3_2 100 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 99 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 245 (Polychromatic418967fa.accept_15_8_11_5_1_169 98 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 245 (accept_3_2 97 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 245
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 96 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 245 (Polychromatic418967fa.accept_13_4_10_11_1_1908 95 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 245 (accept_3_2 94 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 101 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 93 101 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 245
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 92 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 101 245 (accept_3_2 91 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 101 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 90 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 245 (Polychromatic418967fa.accept_10_9_1_5_1_594
  89 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 245 (accept_3_2 88
  101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 245
  (Polychromatic418967fa.accept_19_11_6_17_1_9455 87 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 86 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 245 (accept_3_2 85 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 245
  (Polychromatic418967fa.accept_15_8_11_5_1_169 83 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 245 (accept_3_2 82 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 81 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 80 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 245 (accept_3_2 79 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 245 (Polychromatic418967fa.accept_11_1_2_3_1_688 78 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 245
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 77 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 245 (accept_3_2 76 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 245 (Polychromatic418967fa.accept_19_18_6_17_1_8078 75 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  74 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 245 (accept_3_2 73
  101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 245
  (Polychromatic418967fa.accept_21_9_17_14_1_603 72 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 101 245 (Polychromatic418967fa.accept_17_3_16_7_1_5014 71 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 245 (accept_3_2 70 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 101 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 245
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 68 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 101 245 (accept_3_2 67 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 245 (Polychromatic418967fa.accept_19_8_6_17_1_5186 65 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 245 (accept_3_2 64 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 245
  (Polychromatic418967fa.accept_20_3_1_5_1_4643 63 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 101 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 62 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 245 (accept_3_2 61 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 101 245 (Polychromatic418967fa.accept_13_8_10_11_1_2730 60 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 245
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 245 (accept_3_2 58 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 245 (Polychromatic418967fa.accept_17_6_16_7_1_12533 57 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 245 (accept_3_2 55 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 245
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 53 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 101 245 (accept_3_2 52 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 101 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 51 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 245
  (Polychromatic418967fa.accept_19_12_6_17_1_12061 50 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 101 245 (accept_3_2 49 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 101 245 (Polychromatic418967fa.accept_22_4_13_3_1_14748 48 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 245
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 47 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 101 245 (accept_3_2 46 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 101 245 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 245 (accept_3_2 43 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 245
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 42 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 245 (accept_3_2 40 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 245
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 38 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 245 (accept_3_2 37 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 245 (Polychromatic418967fa.accept_20_15_1_5_1_6049 35 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 245 (accept_3_2 34 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 245
  (Polychromatic418967fa.accept_22_11_13_3_1_10106 33 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 245 (Polychromatic418967fa.accept_14_4_3_7_1_3702 32 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 245 (accept_3_2 31 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 245 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 245
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 245 (accept_3_2 28 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 245 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 245 (accept_3_2 25 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 245
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 245 (accept_3_2 22 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 245 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 245 (Polychromatic418967fa.accept_17_3_16_7_1_5014 20 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 245 (accept_3_2 19 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 245 (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 245
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 101 245 (accept_3_2 16 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 101 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  14 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 245 (accept_3_2 13
  101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 245
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 101 245 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 245 (accept_3_2 10 101 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 101 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 101 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 245
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 245 (accept_3_2 7 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 245 (Polychromatic418967fa.accept_21_5_17_14_1_4178 5 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 245 (accept_3_2 4 101 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 101
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 245
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 245 (accept_3_2 1 101 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 245 (allA_of_3_0 100 100 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 245 (allA_succ_of_accept 98 99
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 245 (accept_3_2 97 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 96 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 245 (Polychromatic418967fa.accept_13_4_8_11_1_1937 95 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 245 (accept_3_2 94 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 245 (accept_3_2 91 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 245 (Polychromatic418967fa.accept_15_14_9_5_1_3932 89 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 245 (accept_3_2 88 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 245 (Polychromatic418967fa.accept_13_9_8_11_1_725 87 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 245 (accept_3_2 85 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 245 (Polychromatic418967fa.accept_14_13_1_7_1_1211 83 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 245 (accept_3_2 82 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 245 (accept_3_2 79 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 245 (Polychromatic418967fa.accept_19_1_4_17_1_5136 77 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 245 (accept_3_2 76 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 245 (Polychromatic418967fa.accept_13_10_8_11_1_1985 75 99
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 245 (accept_3_2 73 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 245 (accept_3_2 70 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 245 (accept_3_2 67 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 245 (Polychromatic418967fa.accept_19_8_4_17_1_9510 65 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 245 (accept_3_2 64 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 245 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 245 (accept_3_2 61 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 245 (Polychromatic418967fa.accept_21_18_15_14_1_8871 60 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 245 (Polychromatic418967fa.accept_15_14_9_5_1_3932 59 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 245 (accept_3_2 58 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 245 (accept_3_2 55 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 245 (Polychromatic418967fa.accept_13_1_8_11_1_724 53 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 245 (accept_3_2 52 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 245 (accept_3_2 49 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 245 (Polychromatic418967fa.accept_13_9_8_11_1_725 48 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 245 (Polychromatic418967fa.accept_21_5_15_14_1_2787 47 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 245 (accept_3_2 46 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 245 (accept_3_2 43 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 245 (accept_3_2 40 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 245 (Polychromatic418967fa.accept_19_1_4_17_1_5136 39 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 245 (accept_3_2 37 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 245 (Polychromatic418967fa.accept_13_9_8_11_1_725 35 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 245 (accept_3_2 34 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 245 (accept_3_2 31 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 245 (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 245 (accept_3_2 28 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 245 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 245 (accept_3_2 25 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 245 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 245 (accept_3_2 22 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 245 (accept_3_2 19 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 245 (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 245 (accept_3_2 16 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 245 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 99
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 245 (accept_3_2 13 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 245 (accept_3_2 10 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 245 (accept_3_2 7 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 245 (Polychromatic418967fa.accept_21_5_15_14_1_2787 5 99 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 245 (accept_3_2 4 99 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 245 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 99 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 245 (accept_3_2 1 99 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  245 (allA_succ_of_accept 97 98 245 (accept_3_2 97 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 245 (accept_3_2 94 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 92 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 98 245 7 13 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 98 245 (Polychromatic418967fa.accept_13_12_7_11_1_1935 90 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 89 98
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 245 (accept_3_2 88 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 245 (accept_3_2 85 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98
  245 7 12 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 98 245 (accept_3_2 82 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 98 245 (accept_3_2 79 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 98 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 78
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 98 245 7 11 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 98 245 (accept_3_2 76
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 98 245 (Polychromatic418967fa.accept_13_9_7_11_1_1292 74 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 98 245 (accept_3_2 73 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 98 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 245 7 10 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 98 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 98 245 (accept_3_2 67 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 98 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 98 245 (Polychromatic418967fa.accept_19_8_3_17_1_5181
  65 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 245 (accept_3_2 64
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 98 245 7 9 14 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 98 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 245 (accept_3_2 61 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 245 (accept_3_2 58 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 245 7 8 14 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 245 (accept_3_2 55 98 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 98 245 (Polychromatic418967fa.accept_19_16_3_17_1_6575 54 98
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 98 245
  (Polychromatic418967fa.accept_10_3_8_5_1_606 53 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 98 245 (accept_3_2 52 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 98 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 98 245 49 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 98 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 98 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 98 245 (accept_3_2 46 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 98 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 98 245 (accept_3_2 43 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 245 7 6 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 98 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 245 (accept_3_2 40 98 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 245
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 38 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 245 (accept_3_2 37 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 245 (Polychromatic418967fa.accept_17_2_13_7_1_5011 36 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 98 245 7 5 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 98 245 (accept_3_2 34 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 245 (accept_3_2 31 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 98 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 30
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 245
  (Polychromatic418967fa.accept_11_7_10_3_1_633 29 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 245 7 4 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 98
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 245 (accept_3_2 25 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 98 245 (accept_3_2 22 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98
  245 7 3 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  98 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 98 245 (accept_3_2 19 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 98 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 245 (accept_3_2 16 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 245 7 2 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 245 (accept_3_2 13
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 245 (accept_3_2 10 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 98 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 98 245 7 1 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 98 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 245 (accept_3_2 4 98 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  98 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 245 (accept_3_2 1 98 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  245 (allA_of_3_0 97 97 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 245 (allA_succ_of_accept 95 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 245 (accept_3_2 94 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 245 (Polychromatic418967fa.accept_19_16_1_17_1_8065 92 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 245 (accept_3_2 91 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 245 (Polychromatic418967fa.accept_17_5_11_7_1_6146 90 96
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 245 (accept_3_2 88 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 245 (Polychromatic418967fa.accept_15_12_6_5_1_1275 87 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 245 (accept_3_2 85 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 245
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 83 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 245 (accept_3_2 82 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 81 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 245 (accept_3_2 79 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 78 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 245 (accept_3_2 76 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 74 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 245 (accept_3_2 73 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 245 (accept_3_2 70 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 245 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 245 (accept_3_2 67 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 245
  (Polychromatic418967fa.accept_14_9_12_7_1_597 65 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 245 (accept_3_2 64 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 245 (accept_3_2 61 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 245 (accept_3_2 58 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 245 (accept_3_2 55 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 245 (accept_3_2 52 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 245 (accept_3_2 49 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 245
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 47 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 245 (accept_3_2 46 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 245 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 245 (accept_3_2 43 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 245 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 245 (accept_3_2 40 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 38 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 245 (accept_3_2 37 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 245 (Polychromatic418967fa.accept_21_15_12_14_1_7232 36 96 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 245 (accept_3_2 34 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 245 (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 245 (accept_3_2 31 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 245
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 245 (accept_3_2 28 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 245 (accept_3_2 25 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 245 (accept_3_2 22 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 245 (Polychromatic418967fa.accept_13_7_5_11_1_1927 20 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 245 (accept_3_2 19 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 96 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 245 (accept_3_2 16 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 245 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 245 (accept_3_2 13 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 245
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 245 (accept_3_2 10 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 245 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 245 (accept_3_2 7 96 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 96 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 245 (accept_3_2 4 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 245 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 96 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 245 (accept_3_2 1 96 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 245
  (allA_succ_of_accept 94 95 245 (accept_3_2 94 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 92 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 245 (accept_3_2 91 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 245 5 18 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 245 (accept_3_2 88 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 87
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 245 5 17 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 245 (Polychromatic418967fa.accept_20_3_15_5_1_10631 83 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 245 (accept_3_2 82 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 245 (Polychromatic418967fa.accept_11_4_7_3_1_289
  81 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 245 5 16 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 245 (accept_3_2 79
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 245 (Polychromatic418967fa.accept_13_12_4_11_1_1925 77 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 245 (accept_3_2 76 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 95 245 5 15 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 245 (accept_3_2 73 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 245 (Polychromatic418967fa.accept_13_7_4_11_1_1967 72 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 245 5 14 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 245 (Polychromatic418967fa.accept_16_4_15_5_1_5537 68 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 245 (accept_3_2 67 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 245 5 13 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 245 (accept_3_2 64
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 245
  (Polychromatic418967fa.accept_20_3_15_5_1_10631 63 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 245 (accept_3_2 61 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 245 5 12 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 245 (accept_3_2 58 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 245
  (Polychromatic418967fa.accept_20_16_15_5_1_7740 56 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 245 5 11 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 245 (accept_3_2 52 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 51
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 245 5 10 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 245 (accept_3_2 49
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 245 (accept_3_2 46 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 245 5 9 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 245 (accept_3_2 43 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 245
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 245 5 8 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 245 (accept_3_2 37 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 245
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 95 245 5 7 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 95 245 (accept_3_2 34 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 245 (accept_3_2 31 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95 245 5 6 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 95 245 (Polychromatic418967fa.accept_20_9_15_5_1_4670 29 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 245 (accept_3_2 28 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 245 (Polychromatic418967fa.accept_20_7_15_5_1_6087
  27 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 245 5 5 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 245 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 245 (accept_3_2 22 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 245 5 4 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 245 (accept_3_2 19
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 245 (accept_3_2 16 95 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 245 5 3 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 245 (accept_3_2 13 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 245
  (Polychromatic418967fa.accept_20_11_15_5_1_10632 11 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 95 245 5 2 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 95 245 (Polychromatic418967fa.accept_20_9_15_5_1_4670 9 95 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 245 (accept_3_2 7 95 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 245 5 1 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 245 (accept_3_2 4 95
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 245 (Polychromatic418967fa.accept_9_3_5_2_1_28
  3 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 245 (accept_3_2 1 95 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 245
  (allA_of_3_0 94 94 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 245 (allA_succ_of_accept 92 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 245 (accept_3_2 91 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 245 (Polychromatic418967fa.accept_16_10_13_5_1_3292 90 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 245 (accept_3_2 88 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 245 (accept_3_2 85 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 84 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 245 (Polychromatic418967fa.accept_15_8_3_5_1_608 83 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 245 (accept_3_2 82 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999 81 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 245 (accept_3_2 79 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 245 (accept_3_2 76 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 245 (accept_3_2 73 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 245 (accept_3_2 70 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 245 (accept_3_2 67 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 66 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 245 (Polychromatic418967fa.accept_16_1_13_5_1_2280 65 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 245 (accept_3_2 64 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 93 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 245 (accept_3_2 61 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 245 (accept_3_2 58 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 245 (accept_3_2 55 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 245 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 245 (accept_3_2 52 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 245 (accept_3_2 49 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 245 (accept_3_2 46 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 245 (Polychromatic418967fa.accept_21_3_9_14_1_5701 45 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 245 (accept_3_2 43 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 245 (accept_3_2 40 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 245 (accept_3_2 37 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 245 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 245 (accept_3_2 34 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 245 (accept_3_2 31 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 245 (accept_3_2 28 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 93 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 245 (accept_3_2 25 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 245 (accept_3_2 22 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 245 (accept_3_2 19 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 245 (accept_3_2 16 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 245 (accept_3_2 13 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 245 (Polychromatic418967fa.accept_25_11_18_20_1_14747 11 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 245 (accept_3_2 10 93 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 245 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 93 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 245 (accept_3_2 7 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 245 (accept_3_2 4 93 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 245 (accept_3_2 1 93 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 245
  (allA_succ_of_accept 91 92 245 (accept_3_2 91 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 245 (Polychromatic418967fa.accept_13_12_1_11_1_1917 90 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 89 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 245 (accept_3_2 88 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 86 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 245 (accept_3_2 85 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 84 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 83 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 245 (accept_3_2 82 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 245
  (Polychromatic418967fa.accept_21_17_8_14_1_5638 80 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 245 (accept_3_2 79 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 78 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 77 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 245 (accept_3_2 76 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 245 (accept_3_2 73 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 72 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 245 (Polychromatic418967fa.accept_14_1_8_7_1_1253 71 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 245 (accept_3_2 70 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 245
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 245 (accept_3_2 67 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 245 (Polychromatic418967fa.accept_20_6_12_5_1_9151 66 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 245 (accept_3_2 64 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 245
  (Polychromatic418967fa.accept_11_7_4_3_1_302 62 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 245 (accept_3_2 61 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 245 (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 59 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 245 (accept_3_2 58 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 245
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 245 (accept_3_2 55 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 245 (Polychromatic418967fa.accept_21_12_8_14_1_8862 54 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 245 (accept_3_2 52 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 245 (accept_3_2 49 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 47 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 245 (accept_3_2 46 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 245
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 245 (accept_3_2 43 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 245 (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 245 (accept_3_2 40 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 245
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 245 (accept_3_2 37 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 245 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 245 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 245 (accept_3_2 34 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 245
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 32 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 245 (accept_3_2 31 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 245 (Polychromatic418967fa.accept_20_10_12_5_1_4687 30 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 245 (accept_3_2 28 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 245 (accept_3_2 25 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 245 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 245 (accept_3_2 22 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 245
  (Polychromatic418967fa.accept_13_7_1_11_1_732 20 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 245 (accept_3_2 19 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 245 (accept_3_2 16 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 245 (accept_3_2 13 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 245 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 245 (accept_3_2 10 92 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 245
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 245 (accept_3_2 7 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  245 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 245 (Polychromatic418967fa.accept_21_5_8_14_1_5696 5 92 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 245 (accept_3_2 4 92 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 245 (accept_3_2 1 92 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 245
  (allA_of_3_0 91 91 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 245 (allA_succ_of_accept 89 90 245
  (Polychromatic418967fa.accept_11_1_2_3_1_688 89 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 245 (accept_3_2 88 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 245 (Polychromatic418967fa.accept_20_6_10_5_1_10630 86 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 90 245 5 17 18 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 90 245
  (Polychromatic418967fa.accept_20_4_10_5_1_3305 84 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 245 (accept_3_2 82 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 245 (Polychromatic418967fa.accept_19_5_14_17_1_6550 81 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 245 5 16 18 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 245 (accept_3_2 79 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 245 (Polychromatic418967fa.accept_11_1_2_3_1_688
  78 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 245
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 77 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 245 (accept_3_2 76 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90
  245 5 15 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74
  90 245 (Polychromatic418967fa.accept_20_14_10_5_1_2117 74 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 90 245 (accept_3_2 73 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 245 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 245 5 14 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 245
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 69 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 90 245 (Polychromatic418967fa.accept_19_11_14_17_1_6607 68 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 245 (accept_3_2 67 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 90 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 66 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 90 245 5 13 18 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 245 (accept_3_2 64 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 245
  (Polychromatic418967fa.accept_13_10_12_11_1_731 62 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 245 (accept_3_2 61 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90
  245 5 12 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 245 (accept_3_2 58 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 245 (Polychromatic418967fa.accept_14_1_6_7_1_1936 57 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 245 (Polychromatic418967fa.accept_11_1_2_3_1_688 56 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 245 5 11 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 90 245
  (Polychromatic418967fa.accept_19_16_14_17_1_3863 54 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 53 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 245 (accept_3_2 52 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 245 5 10 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 245 (accept_3_2 49
  90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 245
  (Polychromatic418967fa.accept_20_8_10_5_1_6083 48 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 245 (accept_3_2 46 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 90 245 5 9 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 90 245 (Polychromatic418967fa.accept_16_12_10_5_1_5457 44 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 245 (accept_3_2 43 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 245 (Polychromatic418967fa.accept_20_2_10_5_1_6082 42 90
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 245
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 41 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 245 5 8 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 245 (Polychromatic418967fa.accept_20_18_10_5_1_3306 38 90
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 245 (accept_3_2 37 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 245
  (Polychromatic418967fa.accept_13_10_12_11_1_731 36 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 90 245 5 7 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 90 245 (accept_3_2 34 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 245 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 245 (Polychromatic418967fa.accept_17_15_5_7_1_2694 32 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 245 (accept_3_2 31 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 245 5 6 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 245 (Polychromatic418967fa.accept_14_1_6_7_1_1936 29 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 245 (accept_3_2 28 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 245
  (Polychromatic418967fa.accept_17_9_5_7_1_3802 26 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 90 245 5 5 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 90 245 (Polychromatic418967fa.accept_19_5_14_17_1_6550 24 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 245 (accept_3_2 22 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 245 (Polychromatic418967fa.accept_19_2_14_17_1_700
  21 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 245 5 4 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 245 (accept_3_2 19
  90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 245
  (Polychromatic418967fa.accept_20_18_10_5_1_3306 18 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 245 (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 245 (accept_3_2 16 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 90 245 5 3 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 90 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 14 90 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 245 (accept_3_2 13 90 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 245 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 90 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 245 5 2 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 245 (Polychromatic418967fa.accept_17_9_5_7_1_3802 9 90 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 245 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 245 (accept_3_2 7 90 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 245 (Polychromatic418967fa.accept_20_6_10_5_1_10630
  6 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 90 245 5 1 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 245 (accept_3_2 4 90
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 245 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 245
  (Polychromatic418967fa.accept_19_2_14_17_1_700 2 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 245 (accept_3_2 1 90 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 245
  (allA_succ_of_accept 88 89 245 (accept_3_2 88 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 245 (accept_3_2 85 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 245
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 83 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 245 (accept_3_2 82 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 245 (Polychromatic418967fa.accept_17_12_4_7_1_6257 80 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 245 (accept_3_2 79 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 245 (accept_3_2 76 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 74 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 245 (accept_3_2 73 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 245 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 245
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 245 (accept_3_2 70 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 245 (accept_3_2 67 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 245
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 65 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 245 (accept_3_2 64 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 245 (Polychromatic418967fa.accept_17_12_4_7_1_6257 63 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072 62 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 245 (accept_3_2 61 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 245 (accept_3_2 58 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 245 (accept_3_2 55 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 245
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 245 (accept_3_2 52 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 245 (accept_3_2 49 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 245
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 245 (accept_3_2 46 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 245 (Polychromatic418967fa.accept_16_13_9_5_1_3302 45 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 245 (accept_3_2 43 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 245 (accept_3_2 40 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 245 (Polychromatic418967fa.accept_15_8_14_5_1_2089 38 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 245 (accept_3_2 37 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 89 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 245
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 245 (accept_3_2 34 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 245 (accept_3_2 31 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 245
  (Polychromatic418967fa.accept_16_13_9_5_1_3302 29 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 245 (accept_3_2 28 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 245 (Polychromatic418967fa.accept_16_11_9_5_1_4412 27 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 245 (accept_3_2 25 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 245 (accept_3_2 22 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 245 (accept_3_2 19 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 245 (Polychromatic418967fa.accept_19_18_13_17_1_9517 18 89 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 245
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 245 (accept_3_2 16 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 245 (accept_3_2 13 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 245
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 245 (accept_3_2 10 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 245 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 245 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 245 (accept_3_2 7 89 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 245 (accept_3_2 4 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 89 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 245 (accept_3_2 1 89 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 245 (allA_of_3_0 88 88 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 245
  (allA_succ_of_accept 86 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 245 (accept_3_2 85 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 245 (Polychromatic418967fa.accept_10_3_7_5_1_288
  83 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 245 (accept_3_2 82
  87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 245
  (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 245 (accept_3_2 79 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 77
  87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 245 (accept_3_2 76 87
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 245 (accept_3_2 73 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 71
  87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 245 (accept_3_2 70 87
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 245
  (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 245 (accept_3_2 67 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 245
  (Polychromatic418967fa.accept_19_8_11_17_1_9503 65 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 245 (accept_3_2 64 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 245 (accept_3_2 61 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 245 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 245 (accept_3_2 58 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 245 (accept_3_2 55 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 245 (accept_3_2 52 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 245 (accept_3_2 49 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 245
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 47 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 245 (accept_3_2 46 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 245 (accept_3_2 43 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 245 (accept_3_2 40 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 245 (accept_3_2 37 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 245 (accept_3_2 34 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 245 (accept_3_2 31 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 245
  (Polychromatic418967fa.accept_11_7_10_3_1_633 29 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 245 (accept_3_2 28 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 245 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 245 (accept_3_2 25 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 245 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 245 (accept_3_2 22 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 245 (accept_3_2 19 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 245 (accept_3_2 16 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 245 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 245 (accept_3_2 13 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 245
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 245 (accept_3_2 10 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 245 (accept_3_2 7 87 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 245 (accept_3_2 4 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 245 (accept_3_2 1 87 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 245 (allA_succ_of_accept 85 86 245 (accept_3_2 85 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 86 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 245 (accept_3_2 82 86 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 245 (accept_3_2 79 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 245 (accept_3_2 76 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 245
  (Polychromatic418967fa.accept_10_4_6_5_1_74 74 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 245 (accept_3_2 73 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 245 (accept_3_2 70 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 245 (accept_3_2 67 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 245 (Polychromatic418967fa.accept_14_9_2_7_1_1242 65 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 245 (accept_3_2 64 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 245 (accept_3_2 61 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 245 (accept_3_2 58 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 245 (accept_3_2 55 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 245 (accept_3_2 52 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 245
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 245 (accept_3_2 49 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 245 (accept_3_2 46 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 245 (accept_3_2 43 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 245 (accept_3_2 40 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 245
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 245 (accept_3_2 37 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 245 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 245 (accept_3_2 34 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 245 (accept_3_2 31 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 245 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 245 (accept_3_2 28 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 245 (accept_3_2 25 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 245 (accept_3_2 22 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 245 (accept_3_2 19 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 245 (Polychromatic418967fa.accept_19_18_10_17_1_5192 18 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 245 (accept_3_2 16 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 245
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 245 (accept_3_2 13 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 245 (accept_3_2 10 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 245 (accept_3_2 7 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 245 (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 86 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 245 (accept_3_2 4 86 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  2 86 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 245 (accept_3_2 1 86
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 245
  (allA_of_3_0 85 85 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 245 (allA_succ_of_accept 83 84 245
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 83 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 245 (accept_3_2 82 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 245 (accept_3_2 79 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 84 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 84 245 7 11 12 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 84 245 (accept_3_2 76 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 84 245 (Polychromatic418967fa.accept_20_15_4_5_1_7759
  75 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 245
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 74 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 84 245 (accept_3_2 73 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  84 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 84 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 245 7 10 12 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 84 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 245 (accept_3_2 67 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 84 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 65
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 245 (accept_3_2 64 84
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 245 7 9 12 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 245 (accept_3_2 61 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  84 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 84 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 245 (accept_3_2 58 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 245 7 8 12 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 245 (accept_3_2 55 84 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 245 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 84
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 245 (accept_3_2 52 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84 245 7 7 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 84 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 48
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 245
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 47 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 245 (accept_3_2 46 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 245 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 245 (accept_3_2 43 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 245 7 6 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 245 (accept_3_2 40 84 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 245
  (Polychromatic418967fa.accept_16_6_4_5_1_2272 38 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 245 (accept_3_2 37 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 84 245 7 5 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 84 245 (accept_3_2 34 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 245 (accept_3_2 31 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 245 (Polychromatic418967fa.accept_13_4_6_11_1_2017
  30 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 245
  (Polychromatic418967fa.accept_10_9_4_5_1_616 29 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 245 7 4 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 245 (accept_3_2 25 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 245 (accept_3_2 22 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84
  245 7 3 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  84 245 (Polychromatic418967fa.accept_17_3_16_7_1_5014 20 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 84 245 (accept_3_2 19 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 84 245 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 245 (accept_3_2 16 84 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 245 7 2 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 245 (accept_3_2 13
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 245
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 245 (accept_3_2 10 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 245 7 1 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 84 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 245 (accept_3_2 4 84 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 245 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 84 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 245 (Polychromatic418967fa.accept_20_2_4_5_1_13401
  2 84 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 245 (accept_3_2 1 84
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 245
  (allA_succ_of_accept 82 83 245 (accept_3_2 82 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 245 (Polychromatic418967fa.accept_13_3_5_11_1_716 81 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 245 (Polychromatic418967fa.accept_21_17_20_14_1_11808 80 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 245 (accept_3_2 79 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 77 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 245 (accept_3_2 76 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 75 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 245 (accept_3_2 73 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 245
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 71 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 245 (accept_3_2 70 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 245 (Polychromatic418967fa.accept_21_6_20_14_1_8837 69 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 68 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 245 (accept_3_2 67 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 245
  (Polychromatic418967fa.accept_21_2_20_14_1_5649 65 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 245 (accept_3_2 64 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 245 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 245 (accept_3_2 61 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 245 (Polychromatic418967fa.accept_17_9_15_7_1_6212 60 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 245
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 59 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 245 (accept_3_2 58 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 245 (accept_3_2 55 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 245
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 245 (accept_3_2 52 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 245 (Polychromatic418967fa.accept_19_13_7_17_1_9441 51 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 245 (accept_3_2 49 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 245 (accept_3_2 46 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 245 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 245 (accept_3_2 43 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 245
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 245 (accept_3_2 40 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 245 (Polychromatic418967fa.accept_17_5_15_7_1_4992 39 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 245 (accept_3_2 37 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 245 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 245
  (Polychromatic418967fa.accept_19_16_7_17_1_3853 35 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 245 (accept_3_2 34 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 245 (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 245 (accept_3_2 31 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 245
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 245 (accept_3_2 28 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 245 (accept_3_2 25 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 245 (Polychromatic418967fa.accept_16_8_3_5_1_5512 24 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 245
  (Polychromatic418967fa.accept_21_2_20_14_1_5649 23 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 245 (accept_3_2 22 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 245 (Polychromatic418967fa.accept_19_2_7_17_1_12054 21 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 245 (accept_3_2 19 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 245 (accept_3_2 16 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 245 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 245 (accept_3_2 13 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 245
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 245 (accept_3_2 10 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 245 (accept_3_2 7 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 245
  (Polychromatic418967fa.accept_17_5_15_7_1_4992 5 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 245 (accept_3_2 4 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  245 (Polychromatic418967fa.accept_13_3_5_11_1_716 3 83 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 245 (accept_3_2 1 83 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 245 (allA_of_3_0
  82 82 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 245 (allA_succ_of_accept 80 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 245 (accept_3_2 79 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 78 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 245 (Polychromatic418967fa.accept_16_13_1_5_1_5469 77 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 245 (accept_3_2 76 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 245 (accept_3_2 73 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 245 (accept_3_2 70 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 245 (accept_3_2 67 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 245 (Polychromatic418967fa.accept_24_17_9_5_1_7985 65 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 245 (accept_3_2 64 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 245 (accept_3_2 61 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 59 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 245 (accept_3_2 58 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 245 (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 245 (accept_3_2 55 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 245 (Polychromatic418967fa.accept_13_1_3_11_1_1289 53 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 245 (accept_3_2 52 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 245 (accept_3_2 49 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 245 (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 245 (accept_3_2 46 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 245 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 81
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 245 (accept_3_2 43 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 245 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 245 (accept_3_2 40 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 245 (accept_3_2 37 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 245 (Polychromatic418967fa.accept_20_15_1_5_1_6049 35 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 245 (accept_3_2 34 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 245 (accept_3_2 31 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 245 (Polychromatic418967fa.accept_18_12_9_11_1_4370 30 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 245 (accept_3_2 28 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 245 (accept_3_2 25 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 245 (accept_3_2 22 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 245 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 81
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 245 (accept_3_2 19 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 245 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 245 (accept_3_2 16 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 245 (accept_3_2 13 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 245 (accept_3_2 10 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 245 (accept_3_2 7 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 81 245 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 245 (accept_3_2 4 81 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 245 (accept_3_2 1 81 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 245
  (allA_succ_of_accept 79 80 245 (accept_3_2 79 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 245 (accept_3_2 76 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 245 5 15 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 245 (accept_3_2 73 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 245 (Polychromatic418967fa.accept_17_4_12_7_1_8771
  72 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 245
  (Polychromatic418967fa.accept_17_3_12_7_1_4949 71 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 245 5 14 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 245 (accept_3_2 67 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 66
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 245 5 13 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 245 (accept_3_2 64
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 245 (accept_3_2 61 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 80 245 5 12 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 245 (accept_3_2 58 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 245
  (Polychromatic418967fa.accept_13_4_2_11_1_733 56 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 80 245 5 11 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 80 245 (Polychromatic418967fa.accept_17_3_12_7_1_4949 54 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 245 (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 80
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 245 (accept_3_2 52 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 245 5 10 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 245 (accept_3_2 49
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 245 (Polychromatic418967fa.accept_21_5_17_14_1_4178 47 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 245 (accept_3_2 46 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 80 245 5 9 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 80 245 (Polychromatic418967fa.accept_19_6_4_17_1_6540 44 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 245 (accept_3_2 43 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 245 5 8 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 245 (accept_3_2 37 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 245
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 80 245 5 7 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 80 245 (accept_3_2 34 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 245 (accept_3_2 31 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 245 5 6 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 80 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 245 (accept_3_2 28 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 245 5 5 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 245 (accept_3_2 22 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 245 5 4 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 245 (accept_3_2 19
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 245
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 245 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 245 (accept_3_2 16 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 245 5 3 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 245 (accept_3_2 13 80 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 245
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 245 5 2 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 245 (Polychromatic418967fa.accept_19_8_4_17_1_9510 8 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 245 (accept_3_2 7 80 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 245 5 1 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 245 (accept_3_2 4 80
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 245 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 245 (accept_3_2 1 80 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 245 (allA_of_3_0 79
  79 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 245 (allA_succ_of_accept 77 78 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 245 (accept_3_2 76 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 245 (Polychromatic418967fa.accept_16_10_14_5_1_5496 74 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 245 (accept_3_2 73 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 78 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 245 (accept_3_2 70 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 245 (Polychromatic418967fa.accept_14_13_8_7_1_1224 69 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 245 (accept_3_2 67 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 245
  (Polychromatic418967fa.accept_17_14_10_7_1_2670 65 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 245 (accept_3_2 64 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 245 (accept_3_2 61 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 245 (Polychromatic418967fa.accept_19_3_2_17_1_6574 60 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 245 (accept_3_2 58 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 245 (Polychromatic418967fa.accept_20_16_18_5_1_4638 56 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 245 (accept_3_2 55 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 78 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 245 (accept_3_2 52 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 245 (accept_3_2 49 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 245 (accept_3_2 46 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 245 (Polychromatic418967fa.accept_19_7_2_17_1_9426 45 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 245 (accept_3_2 43 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 245 (accept_3_2 40 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 245 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 245 (accept_3_2 37 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 245 (accept_3_2 34 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 245 (accept_3_2 31 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 245
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 29 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 245 (accept_3_2 28 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 245 (accept_3_2 25 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 245 (accept_3_2 22 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 245 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 245 (accept_3_2 19 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 245 (Polychromatic418967fa.accept_17_1_10_7_1_12461 18 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 245 (accept_3_2 16 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 245 (accept_3_2 13 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 245 (accept_3_2 10 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 245 (accept_3_2 7 78 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 245 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 78 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 245 (accept_3_2 4 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 245 (accept_3_2 1 78 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 245 (allA_succ_of_accept 76 77 245 (accept_3_2 76 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 245 (Polychromatic418967fa.accept_15_14_2_5_1_1272 74 77
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 245 (accept_3_2 73 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 245 (Polychromatic418967fa.accept_10_2_7_5_1_605
  72 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 245 7 10 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 245 (accept_3_2 67 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 66
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 245
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 65 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 245 (accept_3_2 64 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  245 7 9 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 245 (accept_3_2 61 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 245 (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 77
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 245 (accept_3_2 58 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 57
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 245 7 8 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 245 (accept_3_2 55
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 245
  (Polychromatic418967fa.accept_19_16_1_17_1_8065 54 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 245 (accept_3_2 52 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 245 (Polychromatic418967fa.accept_16_2_13_5_1_2257
  50 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 245 7 7 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 245 (Polychromatic418967fa.accept_19_9_1_17_1_3879 47 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 245 (accept_3_2 46 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 245 (Polychromatic418967fa.accept_22_1_11_3_1_13278 45 77 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 245 (accept_3_2 43 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77
  245 7 6 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  77 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 245 (accept_3_2 40 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 38 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 245 (accept_3_2 37 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 245
  (Polychromatic418967fa.accept_13_10_12_11_1_731 36 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 77 245 7 5 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 77 245 (accept_3_2 34 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 77 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 245 (accept_3_2 31 77 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 245
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 245 7 4 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 245 (accept_3_2 25 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 245
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 245 (accept_3_2 22 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77
  245 7 3 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  77 245 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 77 245 (accept_3_2 19 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 77 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 245 (accept_3_2 16 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 245 7 2 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 245 (accept_3_2 13
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 245 (accept_3_2 10 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 245 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 77 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 245 7 1 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 245 (Polychromatic418967fa.accept_17_5_9_7_1_6185 5 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 245 (accept_3_2 4 77 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 2
  77 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 245 (accept_3_2 1 77 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 245 (allA_of_3_0 76 76
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 245 (allA_succ_of_accept 74 75 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 245 (accept_3_2 73 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 245 5 14 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 245 (accept_3_2 67 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 245 5 13 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 245 (accept_3_2 64 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 245 (Polychromatic418967fa.accept_19_6_18_17_1_9518 63 75
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 245 (accept_3_2 61 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  245 5 12 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 245 (accept_3_2 58 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 245 5 11 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 245 (accept_3_2 52 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 245 5 10 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 245 (accept_3_2 49 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 245 (Polychromatic418967fa.accept_19_10_18_17_1_8030 48 75
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 245
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 47 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 245 (accept_3_2 46 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  245 5 9 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 245 (accept_3_2 43 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 75 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 245 5 8 15 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 245
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 245 (accept_3_2 37 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 245 (Polychromatic418967fa.accept_20_16_15_5_1_7740 36 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 245 5 7 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 245 (accept_3_2 34 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 245 (accept_3_2 31 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  245 5 6 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 245 (accept_3_2 28 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 245 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 245 5 5 15 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 245 (accept_3_2 22 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 245 5 4 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 245 (accept_3_2 19 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 245 (accept_3_2 16 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  245 5 3 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 245 (accept_3_2 13 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 245 (Polychromatic418967fa.accept_19_11_18_17_1_6538 11 75
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 245 5 2 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 245
  (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 245 (accept_3_2 7 75 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 245 5 1 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 245 (accept_3_2 4 75 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 75 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 245 (accept_3_2 1 75 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 245 (allA_succ_of_accept
  73 74 245 (accept_3_2 73 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 245
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 245 (accept_3_2 70 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  68 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 245 (accept_3_2 67
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 245 (Polychromatic418967fa.accept_17_14_6_7_1_4980 65 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 245 (accept_3_2 64 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072
  62 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 245 (accept_3_2 61
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 245
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 245 (accept_3_2 58 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 245 (Polychromatic418967fa.accept_10_6_4_5_1_615
  56 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 245 (accept_3_2 55
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 245
  (Polychromatic418967fa.accept_13_2_9_11_1_258 54 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 245 (Polychromatic418967fa.accept_13_1_9_11_1_703 53 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 245 (accept_3_2 52 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236
  50 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 245 (accept_3_2 49
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 245
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 48 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 245 (accept_3_2 46 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 245 (accept_3_2 43
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 245
  (Polychromatic418967fa.accept_22_20_8_3_1_13257 42 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 245 (accept_3_2 40 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 38
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 245 (accept_3_2 37 74
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 245 (accept_3_2 34 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 245 (accept_3_2 31
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 245
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 245 (accept_3_2 28 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 245 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 245 (accept_3_2 25
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 245
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 245 (accept_3_2 22 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 245 (accept_3_2 19
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 245
  (Polychromatic418967fa.accept_21_18_11_14_1_8846 18 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 245 (accept_3_2 16 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 245
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 245 (accept_3_2 13 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 245 (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 245 (accept_3_2 10 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 245 (accept_3_2 7 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  245 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 245 (accept_3_2 4 74 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 245 (Polychromatic418967fa.accept_13_2_9_11_1_258 2
  74 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 245 (accept_3_2 1 74 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 245 (allA_of_3_0 73 73 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 245 (allA_succ_of_accept 71 72 245
  (Polychromatic418967fa.accept_17_3_4_7_1_1658 71 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 245 (accept_3_2 70 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 245 (Polychromatic418967fa.accept_13_4_7_11_1_1981 69 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 245 (accept_3_2 67 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 245 (Polychromatic418967fa.accept_13_1_7_11_1_702 66 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 245
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 65 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 245 (accept_3_2 64 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 62 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 245 (accept_3_2 61 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 245 (Polychromatic418967fa.accept_16_12_8_5_1_3316 60 72
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 245
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 59 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 245 (accept_3_2 58 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 245 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 245 (accept_3_2 55 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 245 (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 72
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 245
  (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 245 (accept_3_2 52 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 245 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 245 (Polychromatic418967fa.accept_19_12_15_17_1_3837 50 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 245 (accept_3_2 49 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 72 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 245
  (Polychromatic418967fa.accept_10_7_2_5_1_298 47 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 245 (accept_3_2 46 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 245 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 245 (Polychromatic418967fa.accept_13_5_7_11_1_3470 44 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 245 (accept_3_2 43 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 72 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 245
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 245 (accept_3_2 40 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 245 (accept_3_2 37 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 245
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 245 (accept_3_2 34 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 245 (accept_3_2 31 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 245 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 72 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 245
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 245 (accept_3_2 28 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 245 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 245 (accept_3_2 25 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 72
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 245
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 245 (accept_3_2 22 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 245 (accept_3_2 19 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 245
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 245 (accept_3_2 16 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 245 (Polychromatic418967fa.accept_20_15_12_5_1_11958 15 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 245 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 245 (accept_3_2 13 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 245 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 245
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 11 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 245 (accept_3_2 10 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 245 (accept_3_2 7 72 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 72 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 245
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 245 (accept_3_2 4 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  245 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 72 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 72 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 245 (accept_3_2 1 72 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 245
  (allA_succ_of_accept 70 71 245 (accept_3_2 70 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 245 (accept_3_2 67 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 245
  (Polychromatic418967fa.accept_21_2_8_14_1_4148 65 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 245 (accept_3_2 64 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 245 (accept_3_2 61 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 245 (accept_3_2 58 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 245 (accept_3_2 55 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 245
  (Polychromatic418967fa.accept_15_8_11_5_1_169 53 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 245 (accept_3_2 52 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 245 (accept_3_2 49 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 245
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 47 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 245 (accept_3_2 46 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 245 (Polychromatic418967fa.accept_21_3_8_14_1_8864 45 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 245 (accept_3_2 43 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 245 (accept_3_2 40 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 245 (accept_3_2 37 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 245
  (Polychromatic418967fa.accept_19_16_14_17_1_3863 35 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 71 245 (accept_3_2 34 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 245 (accept_3_2 31 71 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 245
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 245 (accept_3_2 28 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 245 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 245 (accept_3_2 25 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 245 (accept_3_2 22 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 245 (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 245 (accept_3_2 19 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 245
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 245 (accept_3_2 16 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 245 (accept_3_2 13 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 245
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 245 (accept_3_2 10 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 245 (accept_3_2 7 71 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 245 (accept_3_2 4 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 71 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 245 (accept_3_2 1 71 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 245
  (allA_of_3_0 70 70 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 245 (allA_succ_of_accept 68 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 245 (accept_3_2 67 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 245 (Polychromatic418967fa.accept_21_2_6_14_1_1569 65 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 245 (accept_3_2 64 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 245 (accept_3_2 61 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 245 (accept_3_2 58 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 245 (accept_3_2 55 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 245 (accept_3_2 52 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 245 (accept_3_2 49 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 245 (accept_3_2 46 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 245 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 69 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 245 (accept_3_2 43 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 245 (accept_3_2 40 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 245 (accept_3_2 37 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 245 (accept_3_2 34 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 245 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 245 (accept_3_2 31 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 245 (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 245 (accept_3_2 28 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 245 (accept_3_2 25 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 245 (accept_3_2 22 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 245 (accept_3_2 19 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 245 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 245 (accept_3_2 16 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 245 (accept_3_2 13 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 245 (accept_3_2 10 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 245 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 245 (accept_3_2 7 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 245 (accept_3_2 4 69 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 245 (accept_3_2 1 69 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 245 (allA_succ_of_accept 67 68
  245 (accept_3_2 67 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 245 (accept_3_2 64 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 62
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 245 (accept_3_2 61 68
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 59 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 245 (accept_3_2 58 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 245 (Polychromatic418967fa.accept_11_1_2_3_1_688
  56 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 245 (accept_3_2 55
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 245
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 245 (accept_3_2 52 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 245 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 245 (accept_3_2 49
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 245 (accept_3_2 46 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 245 (accept_3_2 43 68
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 245 (accept_3_2 40 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 245 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 245 (accept_3_2 37
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 245
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 245 (accept_3_2 34 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 245 (Polychromatic418967fa.accept_10_2_8_5_1_587
  32 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 245 (accept_3_2 31
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 245 (accept_3_2 28 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 245 (accept_3_2 25 68
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 245 (accept_3_2 22 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 245 (Polychromatic418967fa.accept_13_7_3_11_1_280
  20 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 245 (accept_3_2 19
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 245
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 245 (accept_3_2 16 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 245 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 245 (accept_3_2 13
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 245 (accept_3_2 10 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 245 (accept_3_2 7 68 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 245
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 245 (accept_3_2 4 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 245 (accept_3_2 1 68 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 245
  (allA_of_3_0 67 67 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 245 (allA_succ_of_accept 65 66 245
  (Polychromatic418967fa.accept_19_8_9_17_1_5151 65 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 245 (accept_3_2 64 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 245 (accept_3_2 61 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 245 (accept_3_2 58 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 245 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 245 (accept_3_2 55 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 66 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 245 (accept_3_2 52 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 245 (accept_3_2 49 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 245 (Polychromatic418967fa.accept_13_9_1_11_1_275 48 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 245 (accept_3_2 46 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 245 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 245 (accept_3_2 43 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 245 (accept_3_2 40 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 245 (Polychromatic418967fa.accept_13_12_1_11_1_1917 38 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 245 (accept_3_2 37 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 245 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 66
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 245 (accept_3_2 34 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 245 (accept_3_2 31 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 245 (Polychromatic418967fa.accept_19_11_9_17_1_8038 30 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 245
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 245 (accept_3_2 28 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 245 (accept_3_2 25 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 245 (accept_3_2 22 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 245 (accept_3_2 19 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 245 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 245 (accept_3_2 16 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 245 (accept_3_2 13 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 245 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 245 (accept_3_2 10 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 245 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 245 (accept_3_2 7 66 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 245 (accept_3_2 4 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 245 (Polychromatic418967fa.accept_17_2_15_7_1_6213 2 66 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 245 (accept_3_2 1 66 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 245
  (allA_succ_of_accept 64 65 245 (accept_3_2 64 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 245 (Polychromatic418967fa.accept_16_15_1_5_1_2265 63 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 62 65 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 245 (accept_3_2 61 65 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 245 5 12 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 245 (Polychromatic418967fa.accept_17_8_14_7_1_6203 59 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 245 (accept_3_2 58 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 245 (Polychromatic418967fa.accept_16_9_1_5_1_2282
  57 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 245
  (Polychromatic418967fa.accept_22_12_21_3_1_13256 56 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 65 245 5 11 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 65 245 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 65 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 245
  (Polychromatic418967fa.accept_19_15_8_17_1_9429 53 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 245 (accept_3_2 52 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 65 245 5 10 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 65 245 (accept_3_2 49 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 65 245 (Polychromatic418967fa.accept_19_10_8_17_1_12063 48 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 47 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 245 (accept_3_2 46 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 65 245 5 9 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 65 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 44
  65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 245 (accept_3_2 43 65
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 245
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 42 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 65 245 (Polychromatic418967fa.accept_16_9_1_5_1_2282 41 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 65 245 5 8 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 65 245 (Polychromatic418967fa.accept_23_16_19_15_1_14746 39 65
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 245
  (Polychromatic418967fa.accept_16_6_1_5_1_2242 38 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 245 (accept_3_2 37 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 65 245 5 7 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 65 245 (accept_3_2 34 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 65 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 245 (Polychromatic418967fa.accept_21_11_2_14_1_7225 32 65
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 245 (accept_3_2 31 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65 245 5 6 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 65 245 (Polychromatic418967fa.accept_11_7_10_3_1_633
  29 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 245 (accept_3_2 28
  65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 245
  (Polychromatic418967fa.accept_17_10_14_7_1_2679 27 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 245 (Polychromatic418967fa.accept_14_12_9_7_1_2762 26 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 65 245 5 5 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 245 (Polychromatic418967fa.accept_21_3_2_14_1_7235 24 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 245
  (Polychromatic418967fa.accept_17_6_14_7_1_6115 23 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 245 (accept_3_2 22 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 245 (Polychromatic418967fa.accept_17_4_14_7_1_4965 21 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 65 245 5 4 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 65 245 (accept_3_2 19 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 65 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 245 (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 65
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 245 (accept_3_2 16 65 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65 245 5 3 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 65 245
  (Polychromatic418967fa.accept_23_14_19_15_1_13250 14 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 65 245 (accept_3_2 13 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 65 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 245 (Polychromatic418967fa.accept_19_11_8_17_1_12103 11 65
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 245 5 2 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 245
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 245 (Polychromatic418967fa.accept_17_8_14_7_1_6203 8 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 245 (accept_3_2 7 65 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 245 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 65 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 245 5 1 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 245 (accept_3_2 4 65 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 245 (Polychromatic418967fa.accept_19_3_8_17_1_5213 3 65 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 245
  (Polychromatic418967fa.accept_14_2_9_7_1_5633 2 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 245 (accept_3_2 1 65 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 245 (allA_of_3_0 64 64 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 245 (allA_succ_of_accept 62 63 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 245 (accept_3_2 61 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 245 (Polychromatic418967fa.accept_22_15_19_3_1_3768 59 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 245 (accept_3_2 58 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 245 7 8 9 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 245 (accept_3_2 55 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 245
  (Polychromatic418967fa.accept_15_8_3_5_1_608 53 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 245 (accept_3_2 52 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 245 7 7 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 48
  63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 245 (accept_3_2 46 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  63 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 245 (accept_3_2 43 63 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 245 7 6 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 63 245 (Polychromatic418967fa.accept_19_3_6_17_1_6579 41 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 245 (accept_3_2 40 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 245 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 245 (accept_3_2 37 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 63 245 7 5 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 63 245 (accept_3_2 34 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 245 (accept_3_2 31 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 245
  (Polychromatic418967fa.accept_22_7_19_3_1_5266 29 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 63 245 7 4 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 63 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 245 (accept_3_2 25 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077
  24 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 245
  (Polychromatic418967fa.accept_15_8_3_5_1_608 23 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 245 (accept_3_2 22 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63
  245 7 3 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  63 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 63 245 (accept_3_2 19 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 245 (accept_3_2 16 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 245
  (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 245 7 2 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 245 (accept_3_2 13 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 245 (Polychromatic418967fa.accept_19_11_6_17_1_9455 11 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 245 (accept_3_2 10 63 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 245 7 1 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 63 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 245 (accept_3_2 4 63 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 245 (Polychromatic418967fa.accept_17_3_12_7_1_4949
  3 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 245 (accept_3_2 1 63 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  245))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 245 (allA_succ_of_accept 61 62 245
  (accept_3_2 61 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 245 (accept_3_2 58 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 245 (accept_3_2 55
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 245
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 245 (accept_3_2 52 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 245 (accept_3_2 49 62
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 245 (accept_3_2 46 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 245 (accept_3_2 43
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 245 (accept_3_2 40 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 245 (Polychromatic418967fa.accept_10_8_2_5_1_596
  38 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 245 (accept_3_2 37
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 245
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 245 (accept_3_2 34 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 245 (accept_3_2 31 62
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 245 (accept_3_2 28 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 245 (Polychromatic418967fa.accept_11_4_7_3_1_289
  26 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 245 (accept_3_2 25
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 245 (accept_3_2 22 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 245 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 245 (accept_3_2 19
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 245
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 62 245 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 245 (accept_3_2 16 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 245 (accept_3_2 13 62
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 62 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 245 (accept_3_2 10 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 62 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 8
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 245 (accept_3_2 7 62 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 245 (accept_3_2 4 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 245 (accept_3_2 1 62 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 245
  (allA_of_3_0 61 61 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 245 (allA_succ_of_accept 59 60 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 245 (accept_3_2 58 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 245 (Polychromatic418967fa.accept_13_4_8_11_1_1937 56 60 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 245 5 11 12 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 245
  (Polychromatic418967fa.accept_19_16_3_17_1_6575 54 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 245 (accept_3_2 52 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 245 (Polychromatic418967fa.accept_18_15_6_11_1_5651 51 60 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 245 5 10 12 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 245 (accept_3_2 49 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48
  60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 245
  (Polychromatic418967fa.accept_21_5_18_14_1_2793 47 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 245 (accept_3_2 46 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60
  245 5 9 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  60 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 245 (accept_3_2 43 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 245 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 245 5 8 12 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 245 (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 245 (accept_3_2 37 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 245 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 60 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 245 5 7 12 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 245 (accept_3_2 34 60 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 245 (accept_3_2 31 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  245 5 6 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 245 (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 245 (accept_3_2 28 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 245 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 245 5 5 12 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 245
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 245 (accept_3_2 22 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 245 5 4 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 245 (accept_3_2 19 60 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 245 (Polychromatic418967fa.accept_24_18_12_5_1_13102 18 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 245 (accept_3_2 16 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60
  245 5 3 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  60 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 245 (accept_3_2 13 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 245 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 60 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 245 5 2 12 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 245 (accept_3_2 7 60 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 60 245 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 60 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 245 5 1 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 245 (accept_3_2 4 60 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 245
  (Polychromatic418967fa.accept_17_2_9_7_1_5002 2 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 245 (accept_3_2 1 60 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 245 (allA_succ_of_accept 58 59 245
  (accept_3_2 58 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 245 (accept_3_2 55 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 53
  59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 245 (accept_3_2 52 59
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 245 (accept_3_2 49 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 245 (Polychromatic418967fa.accept_15_2_14_5_1_2072
  47 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 245 (accept_3_2 46
  59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 245
  (Polychromatic418967fa.accept_19_7_2_17_1_9426 45 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 245 (accept_3_2 43 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 245 (accept_3_2 40 59
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 245 (Polychromatic418967fa.accept_9_3_5_2_1_28
  39 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 245 (accept_3_2 37 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 245 (accept_3_2 34 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 245
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 32 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 245 (accept_3_2 31 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 245 (accept_3_2 28 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 245 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 59 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 245 (accept_3_2 25 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 245 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 59 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 245 (accept_3_2 22 59 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 245
  (Polychromatic418967fa.accept_21_20_17_14_1_10489 20 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 59 245 (accept_3_2 19 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 245 (accept_3_2 16 59 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 245 (accept_3_2 13 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 245 (accept_3_2 10 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 245 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 59 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 245 (accept_3_2 7 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 245 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 245 (accept_3_2 4 59 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 245 (accept_3_2 1 59 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 245 (allA_of_3_0 58 58 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 245
  (allA_succ_of_accept 56 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 245 (accept_3_2 55 57 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 54 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 245 (accept_3_2 52 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 245 (accept_3_2 49 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 245
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 245 (accept_3_2 46 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  57 245 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 245 (accept_3_2 43 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 245 (accept_3_2 40 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  57 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 245 (accept_3_2 37 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 245 (accept_3_2 34 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 245 (accept_3_2 31 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 245 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 245
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 245 (accept_3_2 28 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 245 (accept_3_2 25 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 245 (accept_3_2 22 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 245 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 245 (accept_3_2 19 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 245 (accept_3_2 16 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 245 (accept_3_2 13 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 245
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 245 (accept_3_2 10 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 245 (accept_3_2 7 57 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 245 (accept_3_2 4 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  245 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 57 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 245 (accept_3_2 1 57 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 245))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 245
  (allA_succ_of_accept 55 56 245 (accept_3_2 55 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  56 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 56 245 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 245 (accept_3_2 52 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 56 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 56 245 7 7 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 56 245 (Polychromatic418967fa.accept_19_10_18_17_1_8030 48 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 56
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 245 (accept_3_2 46 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 245
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 245 (accept_3_2 43 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  245 7 6 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 56 245 (accept_3_2 40 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 245 (accept_3_2 37 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 245
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 56 245 7 5 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 56 245 (accept_3_2 34 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 56 245 (Polychromatic418967fa.accept_13_6_4_11_1_282 32 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 245 (accept_3_2 31 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 245 (Polychromatic418967fa.accept_19_11_18_17_1_6538 30 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 245
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 245 7 4 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 245 (accept_3_2 25 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 24
  56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 245
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 245 (accept_3_2 22 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56
  245 7 3 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  56 245 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 56 245 (accept_3_2 19 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 56 245 (Polychromatic418967fa.accept_20_18_16_5_1_9137 18 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 56
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 245 (accept_3_2 16 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 245 7 2 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 245 (accept_3_2 13
  56 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 245
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 245 (accept_3_2 10 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469
  8 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 245 7 1 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 245
  (Polychromatic418967fa.accept_13_6_4_11_1_282 6 56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 245 (Polychromatic418967fa.accept_19_5_18_17_1_8017 5 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 245 (accept_3_2 4 56 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  56 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 245 (accept_3_2 1 56 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 245))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 245 (allA_of_3_0 55 55 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 245
  (allA_succ_of_accept 53 54 245 (Polychromatic418967fa.accept_21_11_12_14_1_5670 53 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 245 (accept_3_2 52 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 245 (Polychromatic418967fa.accept_17_16_3_7_1_5028
  50 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 245 (accept_3_2 49
  54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 245
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 245 (accept_3_2 46 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 245 (Polychromatic418967fa.accept_19_7_16_17_1_6567 45 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 245
  (Polychromatic418967fa.accept_14_2_12_7_1_617 44 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 245 (accept_3_2 43 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 245 (Polychromatic418967fa.accept_13_3_2_11_1_1999 42 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 245 (accept_3_2 40 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 245
  (Polychromatic418967fa.accept_17_4_3_7_1_4971 38 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 245 (accept_3_2 37 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 245 (accept_3_2 34 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 245 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 245
  (Polychromatic418967fa.accept_19_13_16_17_1_5140 32 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 54 245 (accept_3_2 31 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 54 245 (Polychromatic418967fa.accept_13_4_2_11_1_733 30 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 54 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 245 (accept_3_2 28 54 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 245 (accept_3_2 25 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 245 (Polychromatic418967fa.accept_21_3_12_14_1_8848 24 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 245 (accept_3_2 22 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 245
  (Polychromatic418967fa.accept_16_4_6_5_1_2245 20 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 245 (accept_3_2 19 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 245 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 245 (accept_3_2 16 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 245
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 245 (accept_3_2 13 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 245 (accept_3_2 10 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 54 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 245
  (Polychromatic418967fa.accept_19_8_16_17_1_6552 8 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 245 (accept_3_2 7 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  245 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 245 (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 245 (accept_3_2 4 54 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 245 (Polychromatic418967fa.accept_14_2_12_7_1_617 2
  54 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 245 (accept_3_2 1 54 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 245))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 245 (allA_succ_of_accept 52 53 245 (accept_3_2 52 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 245 (accept_3_2 49 53 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 48
  53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 245 (accept_3_2 46 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 245 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 245 (accept_3_2 43 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 245 (accept_3_2 40 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 245 (accept_3_2 37 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 245 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 245
  (Polychromatic418967fa.accept_13_9_1_11_1_275 35 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 245 (accept_3_2 34 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 245 (accept_3_2 31 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 245
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 245 (accept_3_2 28 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 245 (accept_3_2 25 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 245 (accept_3_2 22 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 245 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 245 (accept_3_2 19 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 245
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 245 (accept_3_2 16 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 245 (accept_3_2 13 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 245
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 245 (accept_3_2 10 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 245 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 245 (accept_3_2 7 53 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 245 (accept_3_2 4 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 53 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 245 (accept_3_2 1 53 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 245))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 245 (allA_of_3_0 52 52
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 245 (allA_succ_of_accept 50 51 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 245 (accept_3_2 49 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 47 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 245 (accept_3_2 46 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 245 (accept_3_2 43 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 245 (accept_3_2 40 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 245 (accept_3_2 37 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 245 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 245 (accept_3_2 34 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 245 (accept_3_2 31 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 245 (accept_3_2 28 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 245 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 245 (accept_3_2 25 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 245 (accept_3_2 22 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 245 (accept_3_2 19 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 245 (accept_3_2 16 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 245 (accept_3_2 13 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 245 (accept_3_2 10 51 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 245 (accept_3_2 7 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 245 (accept_3_2 4 51 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 245 (accept_3_2 1 51 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 245)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 245 (allA_succ_of_accept 49 50 245 (accept_3_2 49 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 245 (accept_3_2 46 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 245 5 9 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 50 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 245 (accept_3_2 43 50
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 245 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 245 5 8 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 245
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 38 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 245 (accept_3_2 37 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 245 (Polychromatic418967fa.accept_20_16_10_5_1_9133 36 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 245 5 7 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 245 (accept_3_2 34 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 245 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 245 (accept_3_2 31 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 245 5 6 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 245 (Polychromatic418967fa.accept_14_1_8_7_1_1253
  29 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 245 (accept_3_2 28
  50 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 50 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 50 245 5 5 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 50 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 50 245 (accept_3_2 22 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  50 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 50 245 5 4 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 245 (accept_3_2 19 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 50 245 (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 50 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 245 (accept_3_2 16 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 50 245 5 3 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 50 245
  (Polychromatic418967fa.accept_19_14_12_17_1_5196 14 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 50 245 (accept_3_2 13 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 50 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 245 5 2 10 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 50 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 245 (accept_3_2 7 50 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 50 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 50 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 245 5 1 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 245 (accept_3_2 4 50 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 245
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 2 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 245 (accept_3_2 1 50 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  245)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 245 (allA_of_3_0 49 49 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 245 (allA_succ_of_accept 47 48 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47
  48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 245 (accept_3_2 46 48
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 245
  (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 48 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 245 (accept_3_2 43 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 48 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 245 (accept_3_2 40 48
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 245
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 245 (Polychromatic418967fa.accept_15_8_3_5_1_608 38 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 245 (accept_3_2 37 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 48 245 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 245 (accept_3_2 34 48
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 245
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 48 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 245 (accept_3_2 31 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 48 245 (Polychromatic418967fa.accept_20_10_8_5_1_7735 30 48 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 245
  (Polychromatic418967fa.accept_11_7_4_3_1_302 29 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 245 (accept_3_2 28 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 245 (accept_3_2 25 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 245 (accept_3_2 22 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 245 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 245 (Polychromatic418967fa.accept_13_7_9_11_1_705 20 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 245 (accept_3_2 19 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 48 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 245 (accept_3_2 16 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 245 (accept_3_2 13 48 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 245
  (Polychromatic418967fa.accept_21_11_6_14_1_10482 11 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 48 245 (accept_3_2 10 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 48 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 245 (accept_3_2 7 48 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 245 (accept_3_2 4 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  245 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 245 (accept_3_2 1 48 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 245)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 245 (allA_succ_of_accept 46
  47 245 (accept_3_2 46 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 245
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 245 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 245 (accept_3_2 43 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 245 (Polychromatic418967fa.accept_15_11_2_5_1_2076
  41 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 245 (accept_3_2 40
  47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 245
  (Polychromatic418967fa.accept_19_1_9_17_1_8039 39 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 245 (accept_3_2 37 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 245 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 245
  (Polychromatic418967fa.accept_13_9_8_11_1_725 35 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 245 (accept_3_2 34 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 245 (accept_3_2 31 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 245
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 245 (accept_3_2 28 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 245 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 245 (accept_3_2 25 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 245 (Polychromatic418967fa.accept_25_24_22_20_1_14745 24 47 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 245
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 245 (accept_3_2 22 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 245 (Polychromatic418967fa.accept_19_2_9_17_1_626 21 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 245 (Polychromatic418967fa.accept_16_4_15_5_1_5537 20 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 245 (accept_3_2 19 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 245
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 245 (accept_3_2 16 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 245 (Polychromatic418967fa.accept_20_15_7_5_1_2115 15 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 245 (accept_3_2 13 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 245
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 245 (accept_3_2 10 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 245 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 245 (accept_3_2 7 47 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 245
  (Polychromatic418967fa.accept_25_5_22_20_1_14744 5 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 245 (accept_3_2 4 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  245 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 47 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 245 (accept_3_2 1 47 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 245))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 245 (allA_of_3_0 46 46 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 245 (allA_succ_of_accept 44 45 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 245 (accept_3_2 43 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 245 (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 245 (Polychromatic418967fa.accept_16_9_13_5_1_2238 41 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 245 5 8 9 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 245
  (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 245 (accept_3_2 37 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 245 (Polychromatic418967fa.accept_21_15_3_14_1_4141 36 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 245 5 7 9 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 245 (accept_3_2 34 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 245 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 45
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 245 (accept_3_2 31 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45
  245 5 6 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  45 245 (Polychromatic418967fa.accept_19_10_7_17_1_9496 29 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 245 (accept_3_2 28 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 245 5 5 9 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 245
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 245 (Polychromatic418967fa.accept_21_2_3_14_1_5690 23 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 245 (accept_3_2 22 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 245 (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 245 5 4 9 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 245 (accept_3_2 19 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 245 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 45
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 245
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 245 (accept_3_2 16 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45
  245 5 3 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  45 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 245 (accept_3_2 13 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 245 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 245 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 45 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 245 5 2 9 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 245
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 245 (accept_3_2 7 45 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 245 (Polychromatic418967fa.accept_21_6_3_14_1_11869 6 45 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 245 5 1 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 245 (accept_3_2 4 45 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 245 (accept_3_2 1 45 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  245))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 245 (allA_succ_of_accept 43 44 245 (accept_3_2 43 44
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 245 (accept_3_2 40 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 245 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 245 (accept_3_2 37
  44 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 245
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 245 (Polychromatic418967fa.accept_17_1_10_7_1_12461 35 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 245 (accept_3_2 34 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 245 (accept_3_2 31 44
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 245 (accept_3_2 28 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 245 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 245 (accept_3_2 25
  44 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 245 (accept_3_2 22 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 245 (Polychromatic418967fa.accept_13_7_5_11_1_1927
  20 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 245 (accept_3_2 19
  44 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 245
  (Polychromatic418967fa.accept_17_1_10_7_1_12461 18 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 245 (accept_3_2 16 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 245 (accept_3_2 13 44
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 245 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 245 (accept_3_2 10 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 245 (Polychromatic418967fa.accept_15_8_14_5_1_2089
  8 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 245 (accept_3_2 7 44
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 245 (Polychromatic418967fa.accept_9_6_8_2_1_410
  6 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 245 (accept_3_2 4 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 245 (accept_3_2 1 44 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 245)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 245 (allA_of_3_0 43 43 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 245 (allA_succ_of_accept 41 42 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 245 (accept_3_2 40 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 42 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 245 (accept_3_2 37 42 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 245 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 42 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 42 245 7 5 6 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 245 (accept_3_2 34 42 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 245 (accept_3_2 31 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  42 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 42 245 (Polychromatic418967fa.accept_16_13_10_5_1_2278 29 42 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 245 7 4 6 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 42 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 245 (accept_3_2 25 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 42 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 42 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 245 (accept_3_2 22 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42
  245 7 3 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  42 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 42 245 (accept_3_2 19 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 245 (accept_3_2 16 42 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 245 7 2 6 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 245 (accept_3_2 13
  42 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 245 (accept_3_2 10 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 42 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8
  42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 245 7 1 6 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 245
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 245 (accept_3_2 4 42 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287
  2 42 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 245 (accept_3_2 1 42
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 245)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  245 (allA_succ_of_accept 40 41 245 (accept_3_2 40 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 38 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 245 (accept_3_2 37 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 245 (accept_3_2 34 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 245 (accept_3_2 31 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 245
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 245 (accept_3_2 28 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 245 (accept_3_2 25 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 245
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 245 (accept_3_2 22 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 245 (accept_3_2 19 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 245 (Polychromatic418967fa.accept_21_18_20_14_1_5711 18 41 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 245 (accept_3_2 16 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 245 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 245 (accept_3_2 13 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 245
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 245 (accept_3_2 10 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 245 (accept_3_2 7 41 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 245
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 245 (accept_3_2 4 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 41 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 245 (accept_3_2 1 41 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 245))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 245 (allA_of_3_0 40 40 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 245 (allA_succ_of_accept 38 39 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 245 (accept_3_2 37 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 245 (accept_3_2 34 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 245 (accept_3_2 31 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 245 (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 245 (accept_3_2 28 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 39
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 245 (accept_3_2 25 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 245 (accept_3_2 22 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 245 (accept_3_2 19 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 245 (accept_3_2 16 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 245 (accept_3_2 13 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 245 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 245 (accept_3_2 10 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 39 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 245 (accept_3_2 7 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 245 (accept_3_2 4 39 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 245 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 39 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 245 (accept_3_2 1 39 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 245))))))))))))))))))))))))))))))))))))))) (allB_succ 38 245
  (allA_succ_of_accept 37 38 245 (accept_3_2 37 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 245 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 245 (accept_3_2 34 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 245 (accept_3_2 31 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 245 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 245 (accept_3_2 28 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 245
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 245 (accept_3_2 25 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 245 (Polychromatic418967fa.accept_21_3_17_14_1_8828 24 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 245 (accept_3_2 22 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 245 (accept_3_2 19 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 245 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 245 (accept_3_2 16 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 245
  (Polychromatic418967fa.accept_13_1_12_11_1_728 14 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 245 (accept_3_2 13 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 245 (accept_3_2 10 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 245
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 245 (accept_3_2 7 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  245 (Polychromatic418967fa.accept_24_6_14_5_1_14743 6 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 38 245 (Polychromatic418967fa.accept_21_5_17_14_1_4178 5 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 245 (accept_3_2 4 38 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 245 (accept_3_2 1 38 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  245)))))))))))))))))))))))))))))))))))))) (allB_succ 37 245 (allA_of_3_0 37 37 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 245 (allA_succ_of_accept 35 36 245 (Polychromatic418967fa.accept_20_15_16_5_1_7771 35 36 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 245 (accept_3_2 34 36 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 33
  36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 245
  (Polychromatic418967fa.accept_17_15_2_7_1_7389 32 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 245 (accept_3_2 31 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 245 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 245 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 245 (accept_3_2 28 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 245 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 36 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 245
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 245 (accept_3_2 25 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 245 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 245 (Polychromatic418967fa.accept_22_1_14_3_1_14742 23 36 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 245 (accept_3_2 22 36 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 245
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 245 (accept_3_2 19 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 245 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 245 (accept_3_2 16 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 36 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 245
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 245 (accept_3_2 13 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  36 245 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 36 245 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 245 (accept_3_2 10 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 245
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 245 (accept_3_2 7 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  245 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 245 (Polychromatic418967fa.accept_21_5_15_14_1_2787 5 36 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 245 (accept_3_2 4 36 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 245 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 36 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 245 (Polychromatic418967fa.accept_13_2_10_11_1_1276
  2 36 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 245 (accept_3_2 1 36
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 245)))))))))))))))))))))))))))))))))))) (allB_succ 35 245
  (allA_succ_of_accept 34 35 245 (accept_3_2 34 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 245 (accept_3_2 31 35 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 245 5 6 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 35 245 (Polychromatic418967fa.accept_20_9_15_5_1_4670 29 35 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 245 7 4 5 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 245
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 35 245 5 5 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 35 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 245 (accept_3_2 22 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  245 7 3 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 35
  245 5 4 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  35 245 (accept_3_2 19 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 245 (Polychromatic418967fa.accept_20_17_15_5_1_4627 17 35 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 245 (accept_3_2 16 35 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 245 5 3 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 35 245 7 2 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 35 245 (accept_3_2 13 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 35 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 245 (Polychromatic418967fa.accept_17_11_1_7_1_2657 11 35
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 35 245 5 2 7 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 35 245
  (Polychromatic418967fa.accept_20_9_15_5_1_4670 9 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 245 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 35 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 245 7 1 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 245 5 1 7 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 245 (accept_3_2 4 35 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 245 (accept_3_2 1 35 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  245))))))))))))))))))))))))))))))))))) (allB_succ 34 245 (allA_of_3_0 34 34 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 245 (allA_succ_of_accept 32 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 245 (accept_3_2 31 33 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 30
  33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 245
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 245 (accept_3_2 28 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 245 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 245 (accept_3_2 25 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 33 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 245 (accept_3_2 22 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 245 (accept_3_2 19 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 33 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 245 (accept_3_2 16 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 245 (accept_3_2 13 33 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 245
  (Polychromatic418967fa.accept_19_11_14_17_1_6607 11 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 245 (accept_3_2 10 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 245 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 33 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 245 (accept_3_2 7 33 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 245 (Polychromatic418967fa.accept_15_6_3_5_1_607 6
  33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 245 (accept_3_2 4 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 245 (accept_3_2 1 33 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 245))))))))))))))))))))))))))))))))) (allB_succ 32 245 (allA_succ_of_accept 31 32 245
  (accept_3_2 31 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 245 (accept_3_2 28 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 245 (accept_3_2 25 32
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 245 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 245 (accept_3_2 22 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 245
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 20 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 245 (accept_3_2 19 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 245 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 245 (accept_3_2 16 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 245 (accept_3_2 13 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 245 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 245 (accept_3_2 10 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 245 (accept_3_2 7 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 245 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 245 (accept_3_2 4 32 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  32 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 245 (accept_3_2 1 32 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 245)))))))))))))))))))))))))))))))) (allB_succ 31 245
  (allA_of_3_0 31 31 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 245 (allA_succ_of_accept 29 30 245
  (Polychromatic418967fa.accept_20_9_10_5_1_6085 29 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 245 (accept_3_2 28 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 245 5 5 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 24
  30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 245 (accept_3_2 22 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 245 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 30 245 5 4 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 245 (accept_3_2 19 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 30 245 (Polychromatic418967fa.accept_19_18_11_17_1_12083 18 30 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 245 (accept_3_2 16 30
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 245 5 3 6 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 245 (accept_3_2 13 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  30 245 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 30 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 245 5 2 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 245 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9
  30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 245 (accept_3_2 7 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30
  245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 245 5 1 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 245 (accept_3_2 4 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 245 (Polychromatic418967fa.accept_13_2_4_11_1_2003 2 30 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 245 (accept_3_2 1 30 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 245)))))))))))))))))))))))))))))) (allB_succ 29 245 (allA_succ_of_accept 28 29 245
  (accept_3_2 28 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 245
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 29 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 245 (accept_3_2 25 29 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 245
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 245 (accept_3_2 22 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 245 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 245 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 245 (accept_3_2 19 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 245 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 29 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 245
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 245 (accept_3_2 16 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 245 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 245 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 245 (accept_3_2 13 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 245 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 29 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 245
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 245 (accept_3_2 10 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 245 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 245 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 245 (accept_3_2 7 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 245 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 29 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 245
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 245 (accept_3_2 4 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  245 (Polychromatic418967fa.accept_17_3_12_7_1_4949 3 29 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 245 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 245 (accept_3_2 1 29 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 245))))))))))))))))))))))))))))) (allB_succ 28 245 (allA_of_3_0 28 28 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 27 245 (allA_succ_of_accept 26 27 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 245 (accept_3_2 25 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 245 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 245 (accept_3_2 22 27 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 245 (accept_3_2 19 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 245 (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 27 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 245 (accept_3_2 16 27 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 245 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 27
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 245 (accept_3_2 13 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 245 (Polychromatic418967fa.accept_19_11_8_17_1_12103 11 27 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 245 (accept_3_2 10 27 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 245 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 245 (accept_3_2 7 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 245 (Polychromatic418967fa.accept_25_5_2_20_1_14741 5 27 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 245 (accept_3_2 4 27 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 245 (accept_3_2 1 27 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 245))))))))))))))))))))))))))) (allB_succ 26 245
  (allA_succ_of_accept 25 26 245 (accept_3_2 25 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 245 (accept_3_2 22 26 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 245 (accept_3_2 19 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 245 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 245 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 26 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 245 (accept_3_2 16 26 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 245 (accept_3_2 13 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 245 (accept_3_2 10 26 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 245
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 245 (accept_3_2 7 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 245 (accept_3_2 4 26 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 245 (Polychromatic418967fa.accept_14_2_12_7_1_617 2
  26 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 245 (accept_3_2 1 26 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 245)))))))))))))))))))))))))) (allB_succ 25 245 (allA_of_3_0 25
  25 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 245 (allA_succ_of_accept 23 24 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 245 (accept_3_2 22 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 245 (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 245 (accept_3_2 19 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 245 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 24 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 245
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 245 (accept_3_2 16 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 245 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 245 (accept_3_2 13 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 245
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 245 (accept_3_2 10 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 245 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 245 (accept_3_2 7 24 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 245 (accept_3_2 4 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 245 (Polychromatic418967fa.accept_19_2_5_17_1_3850 2 24 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 245 (accept_3_2 1 24 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 245)))))))))))))))))))))))) (allB_succ 23 245 (allA_succ_of_accept 22 23 245 (accept_3_2 22
  23 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 245
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 245 (Polychromatic418967fa.accept_19_1_4_17_1_5136 20 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 245 (accept_3_2 19 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 245 (accept_3_2 16 23
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 245
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 245 (accept_3_2 13 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278
  11 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 245 (accept_3_2 10
  23 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 245
  (Polychromatic418967fa.accept_21_9_2_14_1_7251 9 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 245 (accept_3_2 7 23 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 5
  23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 245 (accept_3_2 4 23 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 245 (accept_3_2 1 23 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  245))))))))))))))))))))))) (allB_succ 22 245 (allA_of_3_0 22 22 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 245 (allA_succ_of_accept 20 21 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 245 (accept_3_2 19 21 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 245 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 245
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 245 (accept_3_2 16 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 21 245 7 2 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 21 245 (accept_3_2 13 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 21 245 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 21 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 21
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 245 (accept_3_2 10 21 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 21 245 7 1 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 21 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 245 (accept_3_2 4 21 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 3
  21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 245 (accept_3_2 1 21 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21
  245))))))))))))))))))))) (allB_succ 20 245 (allA_succ_of_accept 19 20 245 (accept_3_2 19 20 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 245 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 20 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 245 (accept_3_2 16 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20
  245 5 3 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  20 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 20 245 (accept_3_2 13 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 20 245 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 20 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 245 (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 20
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 245 5 2 4 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 20 245 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 20 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 245 (accept_3_2 7 20 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 20 245 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 20 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 245 5 1 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 245 (accept_3_2 4 20 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 245
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 245 (accept_3_2 1 20 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  245)))))))))))))))))))) (allB_succ 19 245 (allA_of_3_0 19 19 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 245 (allA_succ_of_accept 17 18 245 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 18 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 245 (accept_3_2 16 18 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 245
  (Polychromatic418967fa.accept_25_14_18_20_1_14740 14 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 245 (accept_3_2 13 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 18 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 18 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 245 (accept_3_2 10 18 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 245 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9
  18 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 245
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 245 (accept_3_2 7 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  245 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 18 245 (Polychromatic418967fa.accept_19_5_18_17_1_8017 5 18 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 245 (accept_3_2 4 18 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 245
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 245 (accept_3_2 1 18 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  245)))))))))))))))))) (allB_succ 17 245 (allA_succ_of_accept 16 17 245 (accept_3_2 16 17 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 17 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 245
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 245 (accept_3_2 13 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 245 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 17 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 245 (accept_3_2 10 17 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 245 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 17 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 245
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 245 (accept_3_2 7 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 245 (accept_3_2 4 17 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 245 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 2
  17 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 245 (accept_3_2 1 17 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 245))))))))))))))))) (allB_succ 16 245 (allA_of_3_0 16 16 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 245 (allA_succ_of_accept 14 15 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 245 (accept_3_2 13 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 245 (Polychromatic418967fa.accept_20_11_15_5_1_10632 11 15 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 245 5 2 3 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 245
  (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 245 (accept_3_2 7 15 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 245 5 1 3 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 245 (accept_3_2 4 15 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 245 (accept_3_2 1 15 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  245))))))))))))))) (allB_succ 14 245 (allA_succ_of_accept 13 14 245 (accept_3_2 13 14 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  14 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 245 (accept_3_2 10 14
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 245 (Polychromatic418967fa.accept_6_3_2_5_1_32
  9 14 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 245
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 14 245 7 1 2 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 14 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 245 (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 14 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 245 (accept_3_2 4 14 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 245
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 14 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 245 (accept_3_2 1 14 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  245)))))))))))))) (allB_succ 13 245 (allA_of_3_0 13 13 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 245
  (allA_succ_of_accept 11 12 245 (Polychromatic418967fa.accept_21_11_12_14_1_5670 11 12 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 245 (accept_3_2 10 12 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  12 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 245 (accept_3_2 7 12 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  12 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 245 (accept_3_2 4 12 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  245 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 245 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 12 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 245 (accept_3_2 1 12 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 245)))))))))))) (allB_succ 11 245 (allA_succ_of_accept 10 11 245 (accept_3_2 10 11 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  11 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 245
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 11 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 245 (accept_3_2 7 11 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 245 (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 11 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 245 (accept_3_2 4 11 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 245 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 11 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 245 (accept_3_2 1 11 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 245))))))))))) (allB_succ 10 245 (allA_of_3_0 10 10 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 245 (allA_succ_of_accept 8 9 245
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 245 (accept_3_2 7 9 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 245
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 9 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 245 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 9 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 245 (accept_3_2 4 9 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 245 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 245 (accept_3_2 1 9 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 245))))))))) (allB_succ 8 245 (allA_succ_of_accept 7 8 245
  (accept_3_2 7 8 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 245
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 245 (accept_3_2 4 8 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 8
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 245 (accept_3_2 1 8 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 245)))))))) (allB_succ 7 245 (allA_of_3_0 7 7 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 245 (allA_succ_of_accept 5 6 245
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 245 (accept_3_2 4 6 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 245 (Polychromatic418967fa.accept_21_2_6_14_1_1569 2 6 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 245 (accept_3_2 1 6 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 245)))))) (allB_succ 5 245 (allA_succ_of_accept 4 5 245 (accept_3_2 4 5 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 245
  (Polychromatic418967fa.accept_14_2_5_7_1_3767 2 5 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 245 (accept_3_2 1 5 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 245)))))
  (allB_succ 4 245 (allA_of_3_0 4 4 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 245 (allA_succ_of_accept 2
  3 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 245 (accept_3_2 1 3 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 245)))
  (allB_succ 2 245 (allA_succ_of_accept 1 2 245 (accept_3_2 1 2 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  245)) (allB_two
  245)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


