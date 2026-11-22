-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch269_Segment000
-- name    : Polychromatic418967fa_Branch269_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:22.915575+00:00
-- url     : https://prove2.me/theorems/9d8a45b9-c823-428c-8bb3-15c74447ef35
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

def Polychromatic418967fa.branch_269_segment_000 : allB 123 269 :=
  allB_succ 122 269 (allA_succ_of_accept 121 122 269 (accept_3_2 121 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 119 122
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 269 (accept_3_2 118 122
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 117 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 116 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 269 (accept_3_2 115 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 269
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 113 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 122 269 (accept_3_2 112 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 122 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 122
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 269 (accept_3_2 109 122
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 269
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 108 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 122 269 (accept_3_2 106 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 104 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 122 269 (accept_3_2 103 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 122 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 122 269 (accept_3_2 100 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 122 269
  (Polychromatic418967fa.accept_25_23_22_19_1_14732 98 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 122 269 (accept_3_2 97 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 122 269 (accept_3_2 94 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 93
  122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 122 269 (accept_3_2 91 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 122 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 122 269 (Polychromatic418967fa.accept_19_13_8_3_1_2906 89 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 122 269 (accept_3_2 88 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 122 269
  (Polychromatic418967fa.accept_27_5_14_26_1_16427 86 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 122 269 (accept_3_2 85 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 122 269 (accept_3_2 82 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 122 269 (accept_3_2 79 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 122 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 77 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 122 269 (accept_3_2 76 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 122 269 (accept_3_2 73 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 122 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 122 269 (accept_3_2 70 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 122 269 (accept_3_2 67 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 122 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 269 (accept_3_2 64 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 269
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 269 (accept_3_2 61 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 269 (accept_3_2 58 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 269 (accept_3_2 55 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 53 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 269 (accept_3_2 52 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 269
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 269 (accept_3_2 49 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 269 (accept_3_2 46 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 269 (accept_3_2 43 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 41 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 269 (accept_3_2 40 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 269 (accept_3_2 37 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 269 (Polychromatic418967fa.accept_17_2_3_14_1_8043 36 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 269 (accept_3_2 34 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 269 (accept_3_2 31 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 269 (accept_3_2 28 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 269
  (Polychromatic418967fa.accept_22_4_12_5_1_11851 26 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 122 269 (accept_3_2 25 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 269 (accept_3_2 22 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 269 (accept_3_2 19 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 269 (accept_3_2 16 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 269
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 269 (accept_3_2 13 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 269 (accept_3_2 10 122 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 269 (accept_3_2 7 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 269 (accept_3_2 4 122 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 269 (accept_3_2 1 122 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 269 (allA_of_3_0 121 121 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 269
  (allA_succ_of_accept 119 120 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 120 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 269 (accept_3_2 118 120 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 116 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 120 269 (accept_3_2 115 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 120 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 269 (accept_3_2 112 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 269 (Polychromatic418967fa.accept_13_7_3_9_1_1142 111 120
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 120 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 110 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 269 (accept_3_2 109 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 120 269 (Polychromatic418967fa.accept_16_12_8_13_1_6073 108 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 269 (accept_3_2 106 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 120
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 104 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 269 (accept_3_2 103 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 269 (accept_3_2 100 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 99 120
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 269
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 98 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 269 (accept_3_2 97 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 269 (accept_3_2 94 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 269 (accept_3_2 91 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 269 (Polychromatic418967fa.accept_13_12_3_9_1_4341 90 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 269 (accept_3_2 88 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 120 269 (accept_3_2 85 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 120 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 84 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 120 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 269 (accept_3_2 82 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 269
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 80 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 269 (accept_3_2 79 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 269 (accept_3_2 76 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 269 (accept_3_2 73 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 71 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 269 (accept_3_2 70 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 120 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 269 (accept_3_2 67 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 269 (Polychromatic418967fa.accept_19_9_6_3_1_5563 66 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 269 (accept_3_2 64 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 269 (Polychromatic418967fa.accept_18_9_12_17_1_6060 63 120 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 269
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 62 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 269 (accept_3_2 61 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 269 (accept_3_2 58 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 269 (accept_3_2 55 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 269 (accept_3_2 52 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 269 (accept_3_2 49 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 269 (accept_3_2 46 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 269 (accept_3_2 43 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 269 (accept_3_2 40 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 269 (accept_3_2 37 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 269 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 269 (Polychromatic418967fa.accept_16_3_8_13_1_3867 35 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 269 (accept_3_2 34 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 269 (accept_3_2 31 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 269 (accept_3_2 28 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 269 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 120 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 269 (accept_3_2 25 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 269 (accept_3_2 22 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 269 (accept_3_2 19 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 269 (accept_3_2 16 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 269 (accept_3_2 13 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 269 (accept_3_2 10 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 269
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 269 (accept_3_2 7 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 269 (accept_3_2 4 120 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 269 (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 120 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 269 (accept_3_2 1 120 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 269 (allA_succ_of_accept 118 119 269 (accept_3_2 118 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 117 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 269 (Polychromatic418967fa.accept_14_4_7_3_1_1718 116 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 269 (accept_3_2 115 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 114 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 269 (accept_3_2 112 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 110 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 269 (accept_3_2 109 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 269 (Polychromatic418967fa.accept_14_10_7_3_1_1022 108 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 107 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 269 (accept_3_2 106 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592
  105 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 269 (accept_3_2 103 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 269 (Polychromatic418967fa.accept_19_6_5_3_1_11210 101 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 269 (accept_3_2 100 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 269 (Polychromatic418967fa.accept_21_15_14_17_1_5940 99
  119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 269 (accept_3_2 97 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 269 (accept_3_2 94 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 269
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 92 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 269 (accept_3_2 91 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 89 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 269 (accept_3_2 88 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 269 (accept_3_2 85 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 83 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 269 (accept_3_2 82 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 269
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 80 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 269 (accept_3_2 79 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 269 (accept_3_2 76 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 269 (accept_3_2 73 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 71 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 269 (accept_3_2 70 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 269 (accept_3_2 67 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 269 (Polychromatic418967fa.accept_19_8_5_3_1_4181 65 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 269 (accept_3_2 64 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 269 (accept_3_2 61 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 269 (accept_3_2 58 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 269
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 119 269 (accept_3_2 55 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 269 (accept_3_2 52 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 269
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 269 (accept_3_2 49 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 269
  (Polychromatic418967fa.accept_21_5_14_17_1_10616 47 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 119 269 (accept_3_2 46 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 119 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 119 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 269 (accept_3_2 43 119
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2
  42 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 269 (accept_3_2 40 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 269 (accept_3_2 37 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 269 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 269
  (Polychromatic418967fa.accept_19_16_5_3_1_1813 35 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 269 (accept_3_2 34 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 269 (accept_3_2 31 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 269
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 269 (accept_3_2 28 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 269 (accept_3_2 25 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 269 (accept_3_2 22 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 269 (accept_3_2 19 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 269
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 269 (accept_3_2 16 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 269 (accept_3_2 13 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 269
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 269 (accept_3_2 10 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 269 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 269 (Polychromatic418967fa.accept_19_8_5_3_1_4181 8 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 269 (accept_3_2 7 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 269 (accept_3_2 4 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 269 (accept_3_2 1 119 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 269 (allA_of_3_0 118 118 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 269
  (allA_succ_of_accept 116 117 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 269 (accept_3_2 115 117 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 113 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 269 (accept_3_2 112 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 111 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 269 (accept_3_2 109 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 108 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 107 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 269 (accept_3_2 106 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 269 (Polychromatic418967fa.accept_16_9_5_13_1_4972 105 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 269 (accept_3_2 103 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 102 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 269
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 101 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 269 (accept_3_2 100 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 117 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 269 (accept_3_2 97 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 269
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 96 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 269 (Polychromatic418967fa.accept_24_23_21_5_1_9781 95 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 269 (accept_3_2 94 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 269 (accept_3_2 91 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 269 (Polychromatic418967fa.accept_16_10_5_13_1_8591 90 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 269 (Polychromatic418967fa.accept_16_9_5_13_1_4972 89 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 269 (accept_3_2 88 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 269 (accept_3_2 85 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 84 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 269 (Polychromatic418967fa.accept_23_14_2_16_1_9988 83 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 269 (accept_3_2 82 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 81 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 269 (accept_3_2 79 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 269 (Polychromatic418967fa.accept_15_2_12_14_1_1709 77 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 269 (accept_3_2 76 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 269 (accept_3_2 73 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 269 (accept_3_2 70 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 69 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 269 (accept_3_2 67 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 269 (Polychromatic418967fa.accept_16_2_5_13_1_3842 66 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 269 (accept_3_2 64 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 269 (accept_3_2 61 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 269 (Polychromatic418967fa.accept_22_16_7_5_1_8718 60 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 269 (Polychromatic418967fa.accept_25_9_17_19_1_16426 59 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 269 (accept_3_2 58 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 269 (accept_3_2 55 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 269 (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 53 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 269 (accept_3_2 52 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 269 (accept_3_2 49 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 269 (Polychromatic418967fa.accept_15_2_12_14_1_1709 47 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 269 (accept_3_2 46 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 269 (Polychromatic418967fa.accept_21_3_12_17_1_7471 45 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 269 (accept_3_2 43 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 269 (accept_3_2 40 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 269 (accept_3_2 37 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 269 (Polychromatic418967fa.accept_27_8_9_26_1_4766 35 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 269 (accept_3_2 34 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 117
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 269 (accept_3_2 31 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 269 (accept_3_2 28 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 269 (accept_3_2 25 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 269 (accept_3_2 22 117 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 269 (Polychromatic418967fa.accept_23_21_2_16_1_16403 21 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 269 (accept_3_2 19 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 269 (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 269 (accept_3_2 16 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 269 (accept_3_2 13 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 269 (accept_3_2 10 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 269 (accept_3_2 7 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 269 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 269 (Polychromatic418967fa.accept_21_5_12_17_1_10634 5 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 269 (accept_3_2 4 117 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 117 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 269 (accept_3_2 1 117 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 269 (allA_succ_of_accept 115 116 269 (accept_3_2 115 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 114 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 269 (Polychromatic418967fa.accept_7_1_4_3_1_21
  113 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 269 (accept_3_2
  112 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 110 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 269 (accept_3_2 109 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 108 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 269
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 107 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 116 269 (accept_3_2 106 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 104 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 269 (accept_3_2 103 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 269
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 102 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 116 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 101 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 116 269 (accept_3_2 100 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 116 269
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 98 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 116 269 (accept_3_2 97 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 116 269 (Polychromatic418967fa.accept_19_1_2_3_1_6995 96 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 116 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 95 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 116 269 (accept_3_2 94 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 116 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 92 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 116 269 (accept_3_2 91 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 116 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 89 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 116 269 (accept_3_2 88 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 116 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 86 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 116 269 (accept_3_2 85 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 116 269 (Polychromatic418967fa.accept_23_15_1_16_1_13301 84 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 116 269 (accept_3_2 82 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 116 269
  (Polychromatic418967fa.accept_25_5_16_19_1_16425 80 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 116 269 (accept_3_2 79 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 116 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 269 (Polychromatic418967fa.accept_14_7_4_3_1_488 77 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 116 269 (accept_3_2 76 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 116 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 269 (accept_3_2 73 116 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 116 269 (Polychromatic418967fa.accept_15_12_11_14_1_3464 72 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 269 (accept_3_2 70 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 269 (accept_3_2 67 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 269 (Polychromatic418967fa.accept_23_20_1_16_1_13265 66
  116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 269 (accept_3_2 64 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 269 (accept_3_2 61 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 269 (Polychromatic418967fa.accept_13_8_12_9_1_1168 60 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 269
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 59 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 269 (accept_3_2 58 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 269 (accept_3_2 55 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 269
  (Polychromatic418967fa.accept_10_3_6_9_1_779 53 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 269 (accept_3_2 52 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 269 (accept_3_2 49 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 269
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 269 (accept_3_2 46 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 269 (Polychromatic418967fa.accept_16_12_4_13_1_3827 44 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 269 (accept_3_2 43 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 269 (accept_3_2 40 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 269 (accept_3_2 37 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 269
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 269 (accept_3_2 34 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 269 (accept_3_2 31 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 269 (Polychromatic418967fa.accept_19_11_2_3_1_8424 30 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 269 (accept_3_2 28 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 269 (accept_3_2 25 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 269 (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 269
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 269 (accept_3_2 22 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 269 (accept_3_2 19 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 116 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 269 (accept_3_2 16 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 269 (accept_3_2 13 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 116
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 269
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 11 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 269 (accept_3_2 10 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 269 (accept_3_2 7 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 116 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 269
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 269 (accept_3_2 4 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 269 (accept_3_2 1 116 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 269 (allA_of_3_0 115 115 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 269
  (allA_succ_of_accept 113 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 113 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 269 (accept_3_2 112 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 110 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 269 (accept_3_2 109 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 108 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 269 (accept_3_2 106 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 105 114
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 104 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 269 (accept_3_2 103 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 114 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 101 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 269 (accept_3_2 100 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 269 (accept_3_2 97 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 114 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 269 (accept_3_2 94 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 92 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 269 (accept_3_2 91 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 269 (accept_3_2 88 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 269 (accept_3_2 85 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 269 (accept_3_2 82 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 114 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 269
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 80 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 269 (accept_3_2 79 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 269 (accept_3_2 76 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 269 (accept_3_2 73 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 114 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 269 (accept_3_2 70 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 269 (accept_3_2 67 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 114 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 269 (accept_3_2 64 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 269 (accept_3_2 61 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 269 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 269 (accept_3_2 58 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 269 (accept_3_2 55 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 269 (accept_3_2 52 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 269 (accept_3_2 49 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 269 (accept_3_2 46 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 269
  (Polychromatic418967fa.accept_20_4_14_9_1_10822 44 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 269 (accept_3_2 43 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 114 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  41 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 269 (accept_3_2 40
  114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 269 (accept_3_2 37 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 269 (accept_3_2 34
  114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 114 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 269 (accept_3_2 31 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257
  29 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 269 (accept_3_2 28
  114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 114 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 269 (accept_3_2 25 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 269 (Polychromatic418967fa.accept_20_4_14_9_1_10822 24 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 269 (accept_3_2 22 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 269 (accept_3_2 19 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 269
  (Polychromatic418967fa.accept_22_17_4_5_1_16424 17 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 114 269 (accept_3_2 16 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 269 (accept_3_2 13 114 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 269 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 269 (accept_3_2 10 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 269 (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 269 (accept_3_2 7 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 269 (accept_3_2 4 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 269 (accept_3_2 1 114 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 269 (allA_succ_of_accept 112 113 269 (accept_3_2 112 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 111 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 110 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 269 (accept_3_2 109 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 269
  (Polychromatic418967fa.accept_8_4_1_5_1_186 108 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 269 (accept_3_2 106 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 269
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 104 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 269 (accept_3_2 103 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 269 (accept_3_2 100 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 99 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 269
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 98 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 269 (accept_3_2 97 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 269 (accept_3_2 94 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 269
  (Polychromatic418967fa.accept_8_4_1_5_1_186 92 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 269 (accept_3_2 91 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 269 (Polychromatic418967fa.accept_19_14_18_3_1_12569 90 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 269 (accept_3_2 88 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 113 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 269 (accept_3_2 85 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 269 (accept_3_2 82 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 269
  (Polychromatic418967fa.accept_15_5_8_14_1_432 80 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 269 (accept_3_2 79 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 269 (Polychromatic418967fa.accept_21_14_8_17_1_15010 77 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 269 (accept_3_2 76 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 113 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 269 (accept_3_2 73 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 269 (Polychromatic418967fa.accept_17_3_11_14_1_2071 71 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 269 (accept_3_2 70 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 113 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 269 (accept_3_2 67 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 269 (accept_3_2 64 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 269
  (Polychromatic418967fa.accept_16_14_1_13_1_2754 62 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 113 269 (accept_3_2 61 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 269 (Polychromatic418967fa.accept_17_8_11_14_1_6770 59 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 269 (accept_3_2 58 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 113 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 269 (accept_3_2 55 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277
  53 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 269 (accept_3_2 52
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 113 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 50 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 269 (accept_3_2 49 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 113 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103
  47 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 269 (accept_3_2 46
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 269
  (Polychromatic418967fa.accept_21_3_8_17_1_7438 45 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 269 (accept_3_2 43 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 269 (Polychromatic418967fa.accept_11_8_3_5_1_355
  41 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 269 (accept_3_2 40
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 113 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 269 (accept_3_2 37 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 113 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 269 (Polychromatic418967fa.accept_15_5_8_14_1_432
  35 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 269 (accept_3_2 34
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 269 (accept_3_2 31 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 269 (accept_3_2 28
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 269
  (Polychromatic418967fa.accept_28_27_1_17_1_16394 27 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 269 (accept_3_2 25 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 269 (accept_3_2 22 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 269 (accept_3_2 19 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 269
  (Polychromatic418967fa.accept_22_17_3_5_1_16423 17 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 113 269 (accept_3_2 16 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 113 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 269 (accept_3_2 13 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 113 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 269 (accept_3_2 10 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 8
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 269 (accept_3_2 7 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 269
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 113 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 269 (accept_3_2 4 113 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 113 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  113 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 269 (accept_3_2 1 113
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 269 (allA_of_3_0 112 112 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 269
  (allA_succ_of_accept 110 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 269 (accept_3_2 109 111 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 108 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 107 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 269 (accept_3_2 106 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 269 (accept_3_2 103 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 101 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 269 (accept_3_2 100 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 99 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 269 (accept_3_2 97 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 95 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 269 (accept_3_2 94 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 269 (accept_3_2 91 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 269
  (Polychromatic418967fa.accept_13_11_7_9_1_612 89 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 269 (accept_3_2 88 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 269 (accept_3_2 85 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 269 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 269 (accept_3_2 82 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 269 (accept_3_2 79 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 269 (accept_3_2 76 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 269 (accept_3_2 73 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 269
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 71 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 269 (accept_3_2 70 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 269 (accept_3_2 67 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 269 (accept_3_2 64 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 269 (accept_3_2 61 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 269 (accept_3_2 58 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 269 (accept_3_2 55 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 269 (accept_3_2 52 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 269 (accept_3_2 49 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 269 (accept_3_2 46 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 269 (accept_3_2 43 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 269 (accept_3_2 40 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 269 (accept_3_2 37 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 269 (Polychromatic418967fa.accept_19_17_16_3_1_8401 36 111 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 269 (accept_3_2 34 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 269 (accept_3_2 31 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 269 (accept_3_2 28 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 269 (Polychromatic418967fa.accept_31_27_18_21_1_16422 27 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 269 (accept_3_2 25 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 269 (accept_3_2 22 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 269 (accept_3_2 19 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 269
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 269 (accept_3_2 16 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 269 (accept_3_2 13 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 269 (accept_3_2 10 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 269 (accept_3_2 7 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 269 (accept_3_2 4 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 111 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 269 (accept_3_2 1 111 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 269 (allA_succ_of_accept 109 110 269 (accept_3_2 109 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 108 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50
  107 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 269 (accept_3_2
  106 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 269 (accept_3_2 103 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 269
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 101 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 110 269 (accept_3_2 100 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 110 269 (Polychromatic418967fa.accept_13_7_6_9_1_1831 98 110
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 269 (accept_3_2 97 110
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 269
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 110 269 (accept_3_2 94 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 110 269 (Polychromatic418967fa.accept_7_1_5_3_1_268
  92 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 269 (accept_3_2 91
  110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 269
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 90 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 110 269 (Polychromatic418967fa.accept_14_5_12_3_1_3397 89 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 110 269 (accept_3_2 88 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 110 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 86 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 110 269 (accept_3_2 85 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 110 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 110 269 (accept_3_2 82 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 110 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 110 269 (accept_3_2 79 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 110 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 110 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 110 269 (accept_3_2 76 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 110 269
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 74 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 110 269 (accept_3_2 73 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 110 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 110 269 (accept_3_2 70 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69
  110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 110 269 (accept_3_2 67 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 269 (accept_3_2 64 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 269
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 269 (accept_3_2 61 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 269 (accept_3_2 58 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 269 (accept_3_2 55 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 269 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 269 (accept_3_2 52 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 269 (accept_3_2 49 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 269 (accept_3_2 46 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 269 (accept_3_2 43 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 269 (accept_3_2 40 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 269
  (Polychromatic418967fa.accept_15_8_5_14_1_986 38 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 269 (accept_3_2 37 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 269 (accept_3_2 34 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 269 (accept_3_2 31 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 269 (accept_3_2 28 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 269
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 110 269 (accept_3_2 25 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 110 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 269 (accept_3_2 22 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 269 (accept_3_2 19 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 269 (Polychromatic418967fa.accept_19_18_15_3_1_5548 18 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 269 (accept_3_2 16 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 269 (accept_3_2 13 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 269 (accept_3_2 10 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 269 (accept_3_2 7 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 269 (accept_3_2 4 110 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 269 (accept_3_2 1 110 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 269 (allA_of_3_0 109 109 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 269
  (allA_succ_of_accept 107 108 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 107 108 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 269 (accept_3_2 106 108 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 105 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 104 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 269 (accept_3_2 103 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 269 (Polychromatic418967fa.accept_19_7_13_3_1_4171 102 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 101 108 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 269 (accept_3_2 100 108 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 269 (Polychromatic418967fa.accept_13_8_4_9_1_1145
  99 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 269
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 98 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 269 (accept_3_2 97 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 269 (Polychromatic418967fa.accept_13_5_4_9_1_601 96 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 95 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 269 (accept_3_2 94 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 269 (Polychromatic418967fa.accept_17_8_6_14_1_6718 93 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 269
  (Polychromatic418967fa.accept_15_2_3_14_1_972 92 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 269 (accept_3_2 91 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 89 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 269 (accept_3_2 88 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 87 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 269
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 86 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 269 (accept_3_2 85 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 108 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 108 269 (Polychromatic418967fa.accept_13_5_4_9_1_601 83 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 269 (accept_3_2 82 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 108 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 269
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 80 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 269 (accept_3_2 79 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 269 (Polychromatic418967fa.accept_21_15_3_17_1_9108 78 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 269 (accept_3_2 76 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 269 (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 269 (accept_3_2 73 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 108 269 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 108 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 71 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 269 (accept_3_2 70 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 269 (Polychromatic418967fa.accept_14_13_10_3_1_1037 69 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 269
  (Polychromatic418967fa.accept_16_4_12_13_1_990 68 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 269 (accept_3_2 67 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 269 (Polychromatic418967fa.accept_17_15_6_14_1_4239 66 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 269 (accept_3_2 64 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 269 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 108 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 269
  (Polychromatic418967fa.accept_11_7_9_5_1_338 62 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 269 (accept_3_2 61 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 269 (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 269 (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 269 (accept_3_2 58 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 108 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 269
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 269 (accept_3_2 55 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 269 (Polychromatic418967fa.accept_49_4_10_24_1_16421 53 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 269 (accept_3_2 52 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 269
  (Polychromatic418967fa.accept_19_12_13_3_1_5447 50 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 108 269 (accept_3_2 49 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 108 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 108 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 269 (accept_3_2 46 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 269
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 108 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 269 (accept_3_2 43 108 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 269 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 269 (accept_3_2 40 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 108 269 (Polychromatic418967fa.accept_20_19_8_9_1_4963 39 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 108 269 (Polychromatic418967fa.accept_22_16_20_5_1_14983 38 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 269 (accept_3_2 37 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 269 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 269
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 269 (accept_3_2 34 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 108 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 269 (accept_3_2 31 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 269 (Polychromatic418967fa.accept_19_11_13_3_1_9820 30 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 269
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 269 (accept_3_2 28 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 269 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 269 (accept_3_2 25 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 269
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 23 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 269 (accept_3_2 22 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 269 (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 269 (accept_3_2 19 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 269 (accept_3_2 16 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 269 (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 269 (accept_3_2 13 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 269 (Polychromatic418967fa.accept_19_12_13_3_1_5447 12 108
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 269
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 269 (accept_3_2 10 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 269 (Polychromatic418967fa.accept_13_8_4_9_1_1145 8 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 269 (accept_3_2 7 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 108 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 269
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 269 (accept_3_2 4 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 269 (Polychromatic418967fa.accept_17_3_6_14_1_4312 3 108 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 269 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 269 (accept_3_2 1 108 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 269 (allA_succ_of_accept 106 107 269 (accept_3_2 106 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 269 (Polychromatic418967fa.accept_19_10_12_3_1_12558 105 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  104 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 269 (accept_3_2
  103 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 101 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 269 (accept_3_2 100 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 269 (accept_3_2 97 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 95 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 269 (accept_3_2 94 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 269 (Polychromatic418967fa.accept_13_2_3_9_1_2610 93 107
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 92 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 269 (accept_3_2 91 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 269 (accept_3_2 88 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 269 (Polychromatic418967fa.accept_15_12_2_14_1_5659 87 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 269 (accept_3_2 85 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 84 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 269 (accept_3_2 82 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 269 (Polychromatic418967fa.accept_34_13_5_31_1_16420 81 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 269
  (Polychromatic418967fa.accept_11_3_8_5_1_336 80 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 269 (accept_3_2 79 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 269 (Polychromatic418967fa.accept_13_12_3_9_1_4341 77 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 269 (accept_3_2 76 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 269 (accept_3_2 73 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 269 (accept_3_2 70 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 269 (accept_3_2 67 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 269 (accept_3_2 64 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 107
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 269 (accept_3_2 61 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 269 (Polychromatic418967fa.accept_13_7_3_9_1_1142 59 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 269 (accept_3_2 58 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 269
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 56 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 107 269 (accept_3_2 55 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 269 (Polychromatic418967fa.accept_17_2_5_14_1_2068 53 107
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 269 (accept_3_2 52 107
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 269
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 269 (accept_3_2 49 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106
  47 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 269 (accept_3_2 46
  107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 269
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 107 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 44 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 269 (accept_3_2 43 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  41 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 269 (accept_3_2 40
  107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 269
  (Polychromatic418967fa.accept_22_17_19_5_1_7044 39 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 269 (accept_3_2 37 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 269
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 269 (accept_3_2 34 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 269 (accept_3_2 31 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 269 (accept_3_2 28 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 269 (accept_3_2 25 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 107 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 269
  (Polychromatic418967fa.accept_24_23_11_5_1_13150 23 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 107 269 (accept_3_2 22 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 107 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 269 (accept_3_2 19 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 269
  (Polychromatic418967fa.accept_19_17_12_3_1_12555 17 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 269 (accept_3_2 16 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 269 (accept_3_2 13 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 269 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 269
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 11 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 107 269 (accept_3_2 10 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 107 269 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 107 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 269 (accept_3_2 7 107 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 269 (accept_3_2 4 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 107 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 269 (accept_3_2 1 107 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 269 (allA_of_3_0 106 106 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 269
  (allA_succ_of_accept 104 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 269 (accept_3_2 103 105 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 269 (accept_3_2 100 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 269 (accept_3_2 97 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 269 (accept_3_2 94 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 269 (accept_3_2 91 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 269 (Polychromatic418967fa.accept_20_10_5_9_1_10908 90 105 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 269
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 89 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 269 (accept_3_2 88 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 87 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 269 (accept_3_2 85 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 269 (accept_3_2 82 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 269 (accept_3_2 79 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 78 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 269 (accept_3_2 76 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 269 (accept_3_2 73 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 269 (Polychromatic418967fa.accept_19_15_10_3_1_12550 72 105 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 269
  (Polychromatic418967fa.accept_10_1_5_9_1_157 71 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 269 (accept_3_2 70 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 269 (Polychromatic418967fa.accept_16_5_9_13_1_3845 69 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 269 (accept_3_2 67 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 269 (accept_3_2 64 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 269 (accept_3_2 61 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 269 (accept_3_2 58 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 269 (accept_3_2 55 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 269
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 269 (accept_3_2 52 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 269 (accept_3_2 49 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 269 (accept_3_2 46 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 269 (accept_3_2 43 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 269 (Polychromatic418967fa.accept_18_6_15_17_1_7363 42 105 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 269 (accept_3_2 40 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 269 (accept_3_2 37 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 269
  (Polychromatic418967fa.accept_20_15_5_9_1_3479 35 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 269 (accept_3_2 34 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 269 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 269 (accept_3_2 31 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 269 (accept_3_2 28 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 269 (accept_3_2 25 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 269 (accept_3_2 22 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 269 (accept_3_2 19 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 269
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 269 (accept_3_2 16 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 269 (accept_3_2 13 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 269 (accept_3_2 10 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 269 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 269 (accept_3_2 7 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 105 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 269 (accept_3_2 4 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 269 (accept_3_2 1 105 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 269 (allA_succ_of_accept 103 104 269 (accept_3_2 103 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 269 (accept_3_2 100 104
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 269 (accept_3_2 97 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271
  95 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 269 (accept_3_2 94
  104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 269 (accept_3_2 91 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 104 269 (Polychromatic418967fa.accept_17_5_2_14_1_4270 90 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 269
  (Polychromatic418967fa.accept_19_13_9_3_1_9806 89 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 269 (accept_3_2 88 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 269 (accept_3_2 85 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 269 (accept_3_2 82 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 80 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 269 (accept_3_2 79 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 269
  (Polychromatic418967fa.accept_21_14_20_17_1_15009 77 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 104 269 (accept_3_2 76 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 269 (accept_3_2 73 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 269 (Polychromatic418967fa.accept_7_2_6_3_1_100
  72 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 269
  (Polychromatic418967fa.accept_17_3_2_14_1_6714 71 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 269 (accept_3_2 70 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 269 (accept_3_2 67 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 269 (accept_3_2 64 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 269 (accept_3_2 61 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 269
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 59 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 104 269 (accept_3_2 58 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 269 (accept_3_2 55 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 269
  (Polychromatic418967fa.accept_17_3_2_14_1_6714 54 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 269 (accept_3_2 52 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 269 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 269 (accept_3_2 49
  104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 104 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 269 (accept_3_2 46 104 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 269 (Polychromatic418967fa.accept_7_2_6_3_1_100
  44 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 269 (accept_3_2 43
  104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 269
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 104 269 (Polychromatic418967fa.accept_27_14_23_26_1_16419 41 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 269 (accept_3_2 40 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 269 (accept_3_2 37 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 269 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 269 (accept_3_2 34 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 269 (accept_3_2 31 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 269 (accept_3_2 28 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 269 (accept_3_2 25 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 269 (accept_3_2 22 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 269 (accept_3_2 19 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 269 (Polychromatic418967fa.accept_27_17_23_26_1_16418 17 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 269 (accept_3_2 16 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 269 (accept_3_2 13 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 269 (accept_3_2 10 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 269 (accept_3_2 7 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 269 (accept_3_2 4 104 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 269 (accept_3_2 1 104 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 269 (allA_of_3_0 103 103 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 269 (allA_succ_of_accept 101
  102 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 269 (accept_3_2 100 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 269 (Polychromatic418967fa.accept_13_7_11_9_1_1858 98 102
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 269 (accept_3_2 97 102
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 269
  (Polychromatic418967fa.accept_9_6_3_8_1_595 96 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 269 (accept_3_2 94 102 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 93 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 92 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 102 269 (accept_3_2 91 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 102 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 102 269 (Polychromatic418967fa.accept_16_9_6_13_1_3831 89 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 269 (accept_3_2 88 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 269 (accept_3_2 85 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 102 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 84 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 269 (accept_3_2 82 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 269
  (Polychromatic418967fa.accept_13_2_11_9_1_591 80 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 269 (accept_3_2 79 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 269 (accept_3_2 76 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 269 (accept_3_2 73 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 269 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 269 (accept_3_2 70 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 269 (accept_3_2 67 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 66 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 269 (accept_3_2 64 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 269 (accept_3_2 61 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 102 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 269 (accept_3_2 58 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 269 (accept_3_2 55 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 269 (accept_3_2 52 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 269 (accept_3_2 49 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 269 (accept_3_2 46 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 269 (Polychromatic418967fa.accept_18_9_12_17_1_6060 45 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 269
  (Polychromatic418967fa.accept_19_6_7_3_1_1733 44 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 269 (accept_3_2 43 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 269 (accept_3_2 40 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 269 (accept_3_2 37 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 269 (accept_3_2 34 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 269 (accept_3_2 31 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 269 (accept_3_2 28 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 269
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 102 269 (accept_3_2 25 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 102 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 269 (accept_3_2 22 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 269 (Polychromatic418967fa.accept_10_1_2_9_1_152
  21 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 269 (accept_3_2 19 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 269 (Polychromatic418967fa.accept_24_18_6_5_1_11477 18 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 269 (accept_3_2 16 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 269 (accept_3_2 13 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 269 (Polychromatic418967fa.accept_19_12_7_3_1_5494 12 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 269 (accept_3_2 10 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 269 (accept_3_2 7 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 269 (accept_3_2 4 102 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 269 (accept_3_2 1 102 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 269 (allA_succ_of_accept 100 101 269 (accept_3_2 100 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 269 (Polychromatic418967fa.accept_19_4_6_3_1_15078 99 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 98 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 269 (accept_3_2 97 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 269
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 269 (accept_3_2 94 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  92 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 269 (accept_3_2 91
  101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 269
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 90 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 269 (Polychromatic418967fa.accept_16_9_5_13_1_4972 89 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 269 (accept_3_2 88 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 269 (accept_3_2 85 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 269 (Polychromatic418967fa.accept_17_15_16_14_1_4291 83 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 269 (accept_3_2 82 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 81 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 269
  (Polychromatic418967fa.accept_19_4_6_3_1_15078 80 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 269 (accept_3_2 79 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 269 (accept_3_2 76 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 269
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 74 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 269 (accept_3_2 73 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 269 (Polychromatic418967fa.accept_13_6_10_9_1_4329 71 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 269 (accept_3_2 70 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 269 (accept_3_2 67 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 65 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 269 (accept_3_2 64 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 269
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 62 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 269 (accept_3_2 61 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 269 (accept_3_2 58 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 269
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 269 (accept_3_2 55 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 269 (Polychromatic418967fa.accept_19_16_6_3_1_6972 54 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 53 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 269 (accept_3_2 52 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 269 (accept_3_2 49 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 269 (Polychromatic418967fa.accept_19_9_6_3_1_5563 47 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 269 (accept_3_2 46 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 269
  (Polychromatic418967fa.accept_27_17_20_26_1_16417 44 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 101 269 (accept_3_2 43 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 269 (accept_3_2 40 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108
  39 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 269
  (Polychromatic418967fa.accept_10_8_1_9_1_413 38 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 269 (accept_3_2 37 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 269 (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 269 (accept_3_2 34 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 269 (accept_3_2 31 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 269 (Polychromatic418967fa.accept_23_6_9_16_1_11687 29 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 269 (accept_3_2 28 101 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 269
  (Polychromatic418967fa.accept_16_10_5_13_1_8591 26 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 101 269 (accept_3_2 25 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 269 (accept_3_2 22 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 269
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 101 269 (accept_3_2 19 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 101 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 269 (accept_3_2 16 101
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 269
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 269 (accept_3_2 13 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 269
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 11 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 269 (accept_3_2 10 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 269 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 101 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 269 (accept_3_2 7 101 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 269 (accept_3_2 4 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 269 (accept_3_2 1 101 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 269 (allA_of_3_0 100 100 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 269 (allA_succ_of_accept 98 99
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 269 (accept_3_2 97 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 269 (accept_3_2 94 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 269 (accept_3_2 91 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 269 (accept_3_2 88 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 87 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 269 (accept_3_2 85 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 269 (Polychromatic418967fa.accept_18_12_9_17_1_7428 84 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 269 (Polychromatic418967fa.accept_15_8_9_14_1_4577 83 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 269 (accept_3_2 82 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 269 (accept_3_2 79 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 269 (accept_3_2 76 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 269 (accept_3_2 73 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 269 (Polychromatic418967fa.accept_21_8_15_17_1_4382 71 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 269 (accept_3_2 70 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 269 (accept_3_2 67 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 269 (accept_3_2 64 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 269 (accept_3_2 61 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 269 (Polychromatic418967fa.accept_13_7_8_9_1_1158 59 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 269 (accept_3_2 58 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 269 (accept_3_2 55 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 269 (accept_3_2 52 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 269 (accept_3_2 49 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 269 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 269 (accept_3_2 46 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 269 (accept_3_2 43 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 269 (Polychromatic418967fa.accept_25_16_24_19_1_16416 41 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 269 (accept_3_2 40 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 269 (accept_3_2 37 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 269 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 269 (accept_3_2 34 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 269 (accept_3_2 31 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 269 (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 269 (accept_3_2 28 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 269 (accept_3_2 25 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 269 (accept_3_2 22 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 269 (accept_3_2 19 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 269 (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 269 (accept_3_2 16 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 269 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 269 (accept_3_2 13 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 269 (accept_3_2 10 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 269 (accept_3_2 7 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 269 (accept_3_2 4 99 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 269 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 99 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 269 (accept_3_2 1 99 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  269 (allA_succ_of_accept 97 98 269 (accept_3_2 97 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 269 (Polychromatic418967fa.accept_15_6_8_14_1_4575 96 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 269 (accept_3_2 94 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 269
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 92 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 269 (accept_3_2 91 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 269 (Polychromatic418967fa.accept_22_2_10_5_1_10424 90 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 89 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 269 (accept_3_2 88 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 269
  (Polychromatic418967fa.accept_13_8_7_9_1_611 86 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 269 (accept_3_2 85 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 269 (accept_3_2 82 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 269 (accept_3_2 79 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 269 (Polychromatic418967fa.accept_17_10_13_14_1_3094 78 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 269 (accept_3_2 76 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 269 (accept_3_2 73 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 269 (accept_3_2 70 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 269 (accept_3_2 67 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 269 (Polychromatic418967fa.accept_15_6_8_14_1_4575 66 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 269 (accept_3_2 64 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 269
  (Polychromatic418967fa.accept_21_20_14_17_1_10643 62 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 98 269 (accept_3_2 61 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 98 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 98 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 269 (accept_3_2 58 98 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57
  98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 269 (accept_3_2 55 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 269 (Polychromatic418967fa.accept_16_5_2_13_1_1007 53 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 269 (accept_3_2 52 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 269
  (Polychromatic418967fa.accept_11_6_10_5_1_341 50 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 269 (accept_3_2 49 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 269 (accept_3_2 46 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 269 (accept_3_2 43 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 269 (accept_3_2 40 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 269
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 38 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 269 (accept_3_2 37 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 269 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 269 (accept_3_2 34 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 269 (accept_3_2 31 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 269 (accept_3_2 28 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 269
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 269 (accept_3_2 25 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 269 (accept_3_2 22 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 269 (accept_3_2 19 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 269 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 269 (accept_3_2 16 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 269 (accept_3_2 13 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 269 (Polychromatic418967fa.accept_23_12_6_16_1_16415 12 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 269 (accept_3_2 10 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 269 (accept_3_2 7 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  269 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 98 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 269 (accept_3_2 4 98 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 269
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 269 (accept_3_2 1 98 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  269 (allA_of_3_0 97 97 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 269 (allA_succ_of_accept 95 96 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 269 (accept_3_2 94 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 269 (accept_3_2 91 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 269
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 89 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 269 (accept_3_2 88 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 269 (Polychromatic418967fa.accept_18_15_6_17_1_2386 87 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 269 (accept_3_2 85 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 269 (accept_3_2 82 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 269 (Polychromatic418967fa.accept_13_3_5_9_1_5285 81 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 80 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 269 (accept_3_2 79 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 269 (accept_3_2 76 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 269 (accept_3_2 73 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 269 (accept_3_2 70 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 269 (accept_3_2 67 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 269 (accept_3_2 64 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 269 (Polychromatic418967fa.accept_19_5_1_3_1_8421 62 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 269 (accept_3_2 61 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 269 (Polychromatic418967fa.accept_25_10_21_19_1_16414 60 96 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 269 (accept_3_2 58 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 269 (accept_3_2 55 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 269
  (Polychromatic418967fa.accept_10_3_6_9_1_779 53 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 269 (accept_3_2 52 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 269 (accept_3_2 49 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 269 (accept_3_2 46 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 269 (accept_3_2 43 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 269 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 269 (accept_3_2 40 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 269 (accept_3_2 37 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 269
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 269 (accept_3_2 34 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 269 (accept_3_2 31 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 269 (accept_3_2 28 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 269 (Polychromatic418967fa.accept_21_5_12_17_1_10634 26 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 269 (accept_3_2 25 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 96 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 269 (accept_3_2 22 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 269 (accept_3_2 19 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 269 (Polychromatic418967fa.accept_27_18_15_26_1_16413 18 96 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 269
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 269 (accept_3_2 16 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 269 (accept_3_2 13 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 269 (accept_3_2 10 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 269 (accept_3_2 7 96 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 269 (Polychromatic418967fa.accept_19_6_1_3_1_11225 6 96 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 269 (accept_3_2 4 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 269 (accept_3_2 1 96 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 269
  (allA_succ_of_accept 94 95 269 (accept_3_2 94 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 269 (accept_3_2 91 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 269
  (Polychromatic418967fa.accept_21_5_11_17_1_10652 89 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 95 269 (accept_3_2 88 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 95 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 95 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 269 (accept_3_2 85 95 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 84
  95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 269 (accept_3_2 82 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 80 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 269 (accept_3_2 79 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 269
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 77 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 269 (accept_3_2 76 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 269 (accept_3_2 73 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 269 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 269 (accept_3_2 70 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 269 (Polychromatic418967fa.accept_15_8_5_14_1_986 68 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 269 (accept_3_2 67 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 269 (accept_3_2 64 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 269 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 269 (accept_3_2 61 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 269
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 269 (accept_3_2 58 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 269 (accept_3_2 55 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 269
  (Polychromatic418967fa.accept_11_9_7_5_1_749 53 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 269 (accept_3_2 52 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 269 (accept_3_2 49 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 269 (accept_3_2 46 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 269 (accept_3_2 43 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 269 (accept_3_2 40 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 269 (accept_3_2 37 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 269
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 269 (accept_3_2 34 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 269 (accept_3_2 31 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 269 (accept_3_2 28 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 269 (accept_3_2 25 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 269
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 269 (accept_3_2 22 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 269 (accept_3_2 19 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 269
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 269 (accept_3_2 16 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 269 (accept_3_2 13 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 269 (accept_3_2 10 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 269 (accept_3_2 7 95 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 269
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 269 (accept_3_2 4 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 269 (accept_3_2 1 95 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 269
  (allA_of_3_0 94 94 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 269 (allA_succ_of_accept 92 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 269 (accept_3_2 91 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 269 (accept_3_2 88 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 269 (accept_3_2 85 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 269 (accept_3_2 82 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 269 (accept_3_2 79 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 269 (accept_3_2 76 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 269 (accept_3_2 73 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 269 (accept_3_2 70 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 269 (accept_3_2 67 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 66 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 269 (accept_3_2 64 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 269 (accept_3_2 61 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 269 (accept_3_2 58 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 269 (accept_3_2 55 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 269 (accept_3_2 52 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 269 (accept_3_2 49 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 269 (accept_3_2 46 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 269 (accept_3_2 43 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 269 (accept_3_2 40 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 269 (accept_3_2 37 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 269 (Polychromatic418967fa.accept_19_16_17_3_1_2916 35 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 269 (accept_3_2 34 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 269 (accept_3_2 31 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 269 (Polychromatic418967fa.accept_20_10_13_9_1_6429 30 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 269 (accept_3_2 28 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 269 (accept_3_2 25 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 269 (accept_3_2 22 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 269 (Polychromatic418967fa.accept_19_2_17_3_1_11224 21 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 269 (accept_3_2 19 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 269 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 269 (accept_3_2 16 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 269 (accept_3_2 13 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 269 (accept_3_2 10 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 269 (Polychromatic418967fa.accept_27_9_12_26_1_16412 9 93 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 269 (accept_3_2 7 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 269 (accept_3_2 4 93 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 269 (accept_3_2 1 93 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 269
  (allA_succ_of_accept 91 92 269 (accept_3_2 91 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 269 (Polychromatic418967fa.accept_16_10_12_13_1_4950 90 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 269 (accept_3_2 88 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 269 (accept_3_2 85 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 83 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 269 (accept_3_2 82 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 269
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 80 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 269 (accept_3_2 79 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 269 (accept_3_2 76 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 269 (accept_3_2 73 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 269 (accept_3_2 70 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 269 (accept_3_2 67 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 269 (accept_3_2 64 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 269 (accept_3_2 61 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 269 (accept_3_2 58 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 269
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 269 (accept_3_2 55 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 269 (accept_3_2 52 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 269 (accept_3_2 49 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 269 (accept_3_2 46 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 269 (accept_3_2 43 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 269 (accept_3_2 40 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 269 (accept_3_2 37 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 269 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 269 (accept_3_2 34 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 269 (accept_3_2 31 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 269 (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 269 (accept_3_2 28 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 269 (accept_3_2 25 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 269 (accept_3_2 22 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 269
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 269 (accept_3_2 19 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 269 (accept_3_2 16 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 269 (accept_3_2 13 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 269 (accept_3_2 10 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 269
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 269 (accept_3_2 7 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 269 (accept_3_2 4 92 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 269 (accept_3_2 1 92 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 269
  (allA_of_3_0 91 91 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 269 (allA_succ_of_accept 89 90 269
  (Polychromatic418967fa.accept_27_8_9_26_1_4766 89 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 269 (accept_3_2 88 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 269 (accept_3_2 85 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 269 (Polychromatic418967fa.accept_19_8_14_3_1_4151 84 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 269 (accept_3_2 82 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 80 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 269 (accept_3_2 79 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 269 (Polychromatic418967fa.accept_16_14_10_13_1_2768 78 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 269
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 77 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 269 (accept_3_2 76 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 269 (accept_3_2 73 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 269 (accept_3_2 70 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 269 (Polychromatic418967fa.accept_16_5_10_13_1_6042 69 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 269 (accept_3_2 67 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 269 (accept_3_2 64 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 62 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 269 (accept_3_2 61 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 90 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 269 (accept_3_2 58 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 269 (Polychromatic418967fa.accept_20_17_10_9_1_6409 57 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 269 (Polychromatic418967fa.accept_19_18_14_3_1_8427 56 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 269 (accept_3_2 55 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 269 (Polychromatic418967fa.accept_19_16_14_3_1_11194 54 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 269 (accept_3_2 52 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 269 (Polychromatic418967fa.accept_26_24_12_9_1_16411 50 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 269 (accept_3_2 49 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 269 (Polychromatic418967fa.accept_22_4_2_5_1_10405 48 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 269 (accept_3_2 46 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 269 (Polychromatic418967fa.accept_19_7_14_3_1_1793 45 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 269 (accept_3_2 43 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 269
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 269 (accept_3_2 40 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 269 (accept_3_2 37 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 269 (accept_3_2 34 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 269 (Polychromatic418967fa.accept_20_13_10_9_1_5030 33 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 269 (accept_3_2 31 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 269
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 269 (accept_3_2 28 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 269 (Polychromatic418967fa.accept_17_9_5_14_1_4277 26 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 269 (accept_3_2 25 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 269 (accept_3_2 22 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 269 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 269 (Polychromatic418967fa.accept_29_20_3_8_1_16410 20 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 269 (accept_3_2 19 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 269
  (Polychromatic418967fa.accept_19_17_14_3_1_5572 17 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 269 (accept_3_2 16 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 269 (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 269 (accept_3_2 13 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 269 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 90
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 269 (accept_3_2 10 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 269 (accept_3_2 7 90 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 269 (Polychromatic418967fa.accept_20_6_10_9_1_3486 6 90 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 269
  (Polychromatic418967fa.accept_16_5_10_13_1_6042 5 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 269 (accept_3_2 4 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 269 (accept_3_2 1 90 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 269 (allA_succ_of_accept 88 89 269 (accept_3_2 88 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 269 (Polychromatic418967fa.accept_16_7_9_13_1_4948 87 89 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 269 (accept_3_2 85 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 269
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 83 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 269 (accept_3_2 82 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 269 (Polychromatic418967fa.accept_16_1_9_13_1_1822 81 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 80 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 269 (accept_3_2 79 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 269
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 77 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 269 (accept_3_2 76 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 269 (Polychromatic418967fa.accept_17_7_4_14_1_2106 75 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 269 (Polychromatic418967fa.accept_21_11_5_17_1_760 74 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 269 (accept_3_2 73 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 269 (accept_3_2 70 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 269 (Polychromatic418967fa.accept_16_5_9_13_1_3845 69 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 269 (accept_3_2 67 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 66 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 269 (accept_3_2 64 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 269 (Polychromatic418967fa.accept_25_13_14_19_1_14711 63 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 269 (Polychromatic418967fa.accept_22_18_1_5_1_14838 62 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 269 (accept_3_2 61 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 269
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 269 (accept_3_2 58 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 269 (Polychromatic418967fa.accept_21_14_5_17_1_16409 56 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 269 (accept_3_2 55 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 269
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 269 (accept_3_2 52 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 269 (accept_3_2 49 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 269 (Polychromatic418967fa.accept_19_10_13_3_1_13772 48 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 269
  (Polychromatic418967fa.accept_13_8_11_9_1_593 47 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 269 (accept_3_2 46 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 269 (Polychromatic418967fa.accept_19_7_13_3_1_4171 45 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 269 (accept_3_2 43 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 269 (Polychromatic418967fa.accept_19_4_13_3_1_5571 42 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 269
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 269 (accept_3_2 40 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 269 (Polychromatic418967fa.accept_16_6_9_13_1_2751 38 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 269 (accept_3_2 37 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 269
  (Polychromatic418967fa.accept_17_1_4_14_1_8058 35 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 269 (accept_3_2 34 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 269 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 269 (Polychromatic418967fa.accept_21_11_5_17_1_760 32 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 269 (accept_3_2 31 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 269 (accept_3_2 28 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 269 (Polychromatic418967fa.accept_14_12_5_3_1_1011 26 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 269 (accept_3_2 25 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 269 (Polychromatic418967fa.accept_17_7_4_14_1_2106 24 89
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 269 (accept_3_2 22 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 269 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 269 (accept_3_2 19 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 269 (Polychromatic418967fa.accept_17_1_4_14_1_8058 18 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 269
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 269 (accept_3_2 16 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 269 (accept_3_2 13 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 269
  (Polychromatic418967fa.accept_19_11_13_3_1_9820 11 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 269 (accept_3_2 10 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 269 (accept_3_2 7 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 89 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 269
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 269 (accept_3_2 4 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  269 (Polychromatic418967fa.accept_22_3_1_5_1_13464 3 89 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 269 (accept_3_2 1 89 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 269
  (allA_of_3_0 88 88 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 269 (allA_succ_of_accept 86 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 269 (accept_3_2 85 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 269 (accept_3_2 82 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 269 (accept_3_2 79 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 269 (accept_3_2 76 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 269 (accept_3_2 73 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 269 (accept_3_2 70 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 269 (accept_3_2 67 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 269 (accept_3_2 64 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 269 (Polychromatic418967fa.accept_18_9_15_17_1_3497 63 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 269 (accept_3_2 61 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 269 (Polychromatic418967fa.accept_18_6_15_17_1_7363 60 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 269 (accept_3_2 58 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 269 (accept_3_2 55 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 269 (Polychromatic418967fa.accept_25_3_12_19_1_16408 53 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 269 (accept_3_2 52 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 269 (Polychromatic418967fa.accept_19_13_11_3_1_5465 51 87
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 269 (accept_3_2 49 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 269 (accept_3_2 46 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 269 (accept_3_2 43 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 269 (accept_3_2 40 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 269 (accept_3_2 37 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 269 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 269 (Polychromatic418967fa.accept_21_14_3_17_1_15004 35 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 269 (accept_3_2 34 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 269 (accept_3_2 31 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 269 (accept_3_2 28 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 269 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 269 (accept_3_2 25 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 269 (accept_3_2 22 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 269 (accept_3_2 19 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 269 (accept_3_2 16 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 269 (accept_3_2 13 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 269 (accept_3_2 10 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 269 (accept_3_2 7 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 269 (accept_3_2 4 87 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 269 (accept_3_2 1 87 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 269
  (allA_succ_of_accept 85 86 269 (accept_3_2 85 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 269 (accept_3_2 82 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 269 (accept_3_2 79 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 269 (accept_3_2 76 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 269 (accept_3_2 73 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 269 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 269 (accept_3_2 70 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 269 (accept_3_2 67 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 269 (accept_3_2 64 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 269 (accept_3_2 61 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 269 (accept_3_2 58 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 269 (accept_3_2 55 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 269 (accept_3_2 52 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 269 (accept_3_2 49 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 269 (accept_3_2 46 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 269 (accept_3_2 43 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 269 (accept_3_2 40 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 269 (accept_3_2 37 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 269 (accept_3_2 34 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 269 (accept_3_2 31 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 269 (accept_3_2 28 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 269 (accept_3_2 25 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 269 (accept_3_2 22 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 269 (accept_3_2 19 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 269 (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 269 (accept_3_2 16 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 269
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 269 (accept_3_2 13 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 269 (accept_3_2 10 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 269 (accept_3_2 7 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 269 (accept_3_2 4 86 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 269 (accept_3_2 1 86 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 269
  (allA_of_3_0 85 85 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 269 (allA_succ_of_accept 83 84 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 269 (accept_3_2 82 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 269 (Polychromatic418967fa.accept_13_2_6_9_1_2636 80 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 269 (accept_3_2 79 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 269 (accept_3_2 76 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 269 (accept_3_2 73 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 269 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 269
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 71 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 269 (accept_3_2 70 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 269 (accept_3_2 67 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 269 (accept_3_2 64 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 269 (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 269 (accept_3_2 61 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 269 (accept_3_2 58 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 269 (accept_3_2 55 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 269 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 269
  (Polychromatic418967fa.accept_10_3_4_9_1_15 53 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 269 (accept_3_2 52 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 269 (accept_3_2 49 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 269 (accept_3_2 46 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 269 (Polychromatic418967fa.accept_16_12_4_13_1_3827 44 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 269 (accept_3_2 43 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 84 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 269 (accept_3_2 40 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 269 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 269 (accept_3_2 37 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 269 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 269
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 269 (accept_3_2 34 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 269 (accept_3_2 31 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 269 (accept_3_2 28 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 269 (Polychromatic418967fa.accept_22_4_18_5_1_5358 26 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 269 (accept_3_2 25 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 269 (accept_3_2 22 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 269 (accept_3_2 19 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 269 (accept_3_2 16 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 269 (accept_3_2 13 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 269 (accept_3_2 10 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 269 (accept_3_2 7 84 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 269 (accept_3_2 4 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  269 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 269 (accept_3_2 1 84 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 269 (allA_succ_of_accept 82 83 269 (accept_3_2 82 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 83 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 80 83 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 269 (accept_3_2 79 83 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 78
  83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 269 (accept_3_2 76 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 269 (accept_3_2 73 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 269
  (Polychromatic418967fa.accept_17_3_15_14_1_4219 71 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 269 (accept_3_2 70 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 269 (accept_3_2 67 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 269 (accept_3_2 64 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 269 (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 269 (accept_3_2 61 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 269 (accept_3_2 58 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 269 (accept_3_2 55 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 269 (accept_3_2 52 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 269 (accept_3_2 49 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 269
  (Polychromatic418967fa.accept_16_15_3_13_1_2818 47 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 269 (accept_3_2 46 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 269 (accept_3_2 43 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 269 (accept_3_2 40 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 269 (accept_3_2 37 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 269
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 269 (accept_3_2 34 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 269 (accept_3_2 31 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 269
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 269 (accept_3_2 28 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 269 (accept_3_2 25 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 269 (accept_3_2 22 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 269 (accept_3_2 19 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 269
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 269 (accept_3_2 16 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 269 (accept_3_2 13 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 269 (accept_3_2 10 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 269 (Polychromatic418967fa.accept_16_8_3_13_1_7295 8 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 269 (accept_3_2 7 83 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 269 (accept_3_2 4 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 269 (accept_3_2 1 83 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 269 (allA_of_3_0 82 82 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 269
  (allA_succ_of_accept 80 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 269 (accept_3_2 79 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 269 (Polychromatic418967fa.accept_13_12_3_9_1_4341
  77 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 269 (accept_3_2 76
  81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 75 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 269 (accept_3_2 73 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 71
  81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 269 (accept_3_2 70 81
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 269 (accept_3_2 67 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 269 (Polychromatic418967fa.accept_18_12_9_17_1_7428 66 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 269 (accept_3_2 64 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 269 (accept_3_2 61 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 269
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 59 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 269 (accept_3_2 58 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 269 (accept_3_2 55 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 269 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 269
  (Polychromatic418967fa.accept_15_8_6_14_1_975 53 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 269 (accept_3_2 52 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 269 (accept_3_2 49 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 269
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 269 (accept_3_2 46 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 269 (accept_3_2 43 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 269 (accept_3_2 40 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 269 (accept_3_2 37 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 269 (accept_3_2 34 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 269 (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 269 (accept_3_2 31 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 269 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 269 (accept_3_2 28 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 269 (accept_3_2 25 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 269
  (Polychromatic418967fa.accept_15_8_6_14_1_975 23 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 269 (accept_3_2 22 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 269 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 269 (accept_3_2 19 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 269
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 269 (accept_3_2 16 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 269 (accept_3_2 13 81 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 269
  (Polychromatic418967fa.accept_22_11_15_5_1_11814 11 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 81 269 (accept_3_2 10 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 81 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 269 (accept_3_2 7 81 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 269 (accept_3_2 4 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 269 (accept_3_2 1 81 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 269 (allA_succ_of_accept 79 80 269 (accept_3_2 79 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 269 (Polychromatic418967fa.accept_24_6_8_5_1_16407 78 80 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 269 (Polychromatic418967fa.accept_14_7_10_3_1_1034 77 80
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 269 (accept_3_2 76 80 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 269
  (Polychromatic418967fa.accept_11_8_3_5_1_355 74 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 269 (accept_3_2 73 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 71 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 269 (accept_3_2 70 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 269
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 68 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 269 (accept_3_2 67 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 66 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 269 (Polychromatic418967fa.accept_19_8_4_3_1_5559 65 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 269 (accept_3_2 64 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 269 (accept_3_2 61 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 269 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 269 (accept_3_2 58 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 269
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 56 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 269 (accept_3_2 55 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 269 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 269 (accept_3_2 52 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 269 (accept_3_2 49 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 269 (accept_3_2 46 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 269
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 269 (accept_3_2 43 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 41 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 269 (accept_3_2 40 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 269 (accept_3_2 37 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 269 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 269 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 269 (accept_3_2 34 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 269
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 32 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 269 (accept_3_2 31 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 269 (accept_3_2 28 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 269 (accept_3_2 25 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 269 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 269 (accept_3_2 22 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 269
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 269 (accept_3_2 19 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 269 (accept_3_2 16 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 269 (accept_3_2 13 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 269 (Polychromatic418967fa.accept_24_12_8_5_1_13088 12 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 269 (accept_3_2 10 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 269
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 269 (accept_3_2 7 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 80 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 269 (accept_3_2 4 80 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 269 (accept_3_2 1 80 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 269 (allA_of_3_0 79
  79 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 269 (allA_succ_of_accept 77 78 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 269 (accept_3_2 76 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 269 (accept_3_2 73 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 269 (accept_3_2 70 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 269 (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 269 (accept_3_2 67 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 269 (accept_3_2 64 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 269 (Polychromatic418967fa.accept_15_2_3_14_1_972 62 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 269 (accept_3_2 61 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 269 (accept_3_2 58 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 269 (accept_3_2 55 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 269 (accept_3_2 52 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 269 (accept_3_2 49 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 269 (accept_3_2 46 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 269 (Polychromatic418967fa.accept_21_3_15_17_1_7487 45 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 269 (accept_3_2 43 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 269 (Polychromatic418967fa.accept_16_10_14_13_1_1870 42 78 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 269 (accept_3_2 40 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 269 (accept_3_2 37 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 269 (Polychromatic418967fa.accept_19_17_2_3_1_4190 36 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 269 (accept_3_2 34 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 269 (accept_3_2 31 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 269 (accept_3_2 28 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 269 (accept_3_2 25 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 269 (accept_3_2 22 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 269 (accept_3_2 19 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 269
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 269 (accept_3_2 16 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 269 (accept_3_2 13 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 269 (accept_3_2 10 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 269 (Polychromatic418967fa.accept_21_8_15_17_1_4382 8 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 269 (accept_3_2 7 78 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 78 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 269 (accept_3_2 4 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 269 (accept_3_2 1 78 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 269 (allA_succ_of_accept 76 77 269 (accept_3_2 76 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 269 (accept_3_2 73 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 269 (Polychromatic418967fa.accept_10_2_7_9_1_783
  72 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 269
  (Polychromatic418967fa.accept_21_8_14_17_1_2968 71 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 269 (accept_3_2 70 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 68 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 269 (accept_3_2 67 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 269 (accept_3_2 64 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 62 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 269 (accept_3_2 61 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 269
  (Polychromatic418967fa.accept_19_2_1_3_1_11216 59 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 269 (accept_3_2 58 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 269 (accept_3_2 55 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 269 (Polychromatic418967fa.accept_19_16_1_3_1_7007 54 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 269
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 269 (accept_3_2 52 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 50 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 269 (accept_3_2 49 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 269 (accept_3_2 46 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 269 (Polychromatic418967fa.accept_21_3_14_17_1_10628 45 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 269 (accept_3_2 43 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 269
  (Polychromatic418967fa.accept_21_20_14_17_1_10643 41 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 269 (accept_3_2 40 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 269 (accept_3_2 37 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 269
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 77 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 269 (accept_3_2 34 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 269 (Polychromatic418967fa.accept_10_2_7_9_1_783
  32 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 269 (accept_3_2 31
  77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 77 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 269 (accept_3_2 28 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 77 269 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 269
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 269 (accept_3_2 25 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 269 (accept_3_2 22 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 269 (accept_3_2 19 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 269 (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 269 (accept_3_2 16 77 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 269
  (Polychromatic418967fa.accept_23_14_8_16_1_16406 14 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 77 269 (accept_3_2 13 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 269 (accept_3_2 10 77 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 269
  (Polychromatic418967fa.accept_21_9_14_17_1_12039 9 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 269 (accept_3_2 7 77 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 77 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693
  5 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 269 (accept_3_2 4 77
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 269 (Polychromatic418967fa.accept_9_3_5_8_1_99
  3 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 269 (accept_3_2 1 77 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 269 (allA_of_3_0 76 76
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 269 (allA_succ_of_accept 74 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 269 (accept_3_2 73 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 269 (accept_3_2 70 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 269 (accept_3_2 67 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 269 (accept_3_2 64 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 269 (Polychromatic418967fa.accept_19_6_18_3_1_11230 63 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 269 (accept_3_2 61 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 269 (accept_3_2 58 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 269 (accept_3_2 55 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 53 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 269 (accept_3_2 52 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 269 (accept_3_2 49 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 269 (Polychromatic418967fa.accept_21_6_12_17_1_13534 48 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 269 (accept_3_2 46 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 269 (accept_3_2 43 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 269 (accept_3_2 40 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 269 (Polychromatic418967fa.accept_26_13_23_9_1_16405 39 75 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 269 (accept_3_2 37 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 269 (Polychromatic418967fa.accept_19_16_18_3_1_15081 35 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 269 (accept_3_2 34 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 269 (accept_3_2 31 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 269 (accept_3_2 28 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 269 (accept_3_2 25 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 269 (accept_3_2 22 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 269 (accept_3_2 19 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 269 (Polychromatic418967fa.accept_23_17_6_16_1_16393 17 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 269 (accept_3_2 16 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 269 (accept_3_2 13 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 269 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 269 (accept_3_2 10 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 269 (accept_3_2 7 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 269 (accept_3_2 4 75 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 269 (Polychromatic418967fa.accept_20_3_15_9_1_6456 3 75 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 269 (accept_3_2 1 75 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 269 (allA_succ_of_accept
  73 74 269 (accept_3_2 73 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 269
  (Polychromatic418967fa.accept_19_15_17_3_1_13760 72 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 269 (accept_3_2 70 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 269 (accept_3_2 67 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 65 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 269 (accept_3_2 64 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 269 (accept_3_2 61 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 269 (accept_3_2 58 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 269 (accept_3_2 55 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 269 (Polychromatic418967fa.accept_17_3_6_14_1_4312 54 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 269 (accept_3_2 52 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 269 (accept_3_2 49 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 269 (accept_3_2 46 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 269 (accept_3_2 43 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 269 (accept_3_2 40 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 269 (accept_3_2 37 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 269 (accept_3_2 34 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 269 (accept_3_2 31 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 269 (accept_3_2 28 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 269
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 269 (accept_3_2 25 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 269 (accept_3_2 22 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 269 (accept_3_2 19 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 269 (Polychromatic418967fa.accept_22_17_8_5_1_16404 17 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 269 (accept_3_2 16 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 269 (accept_3_2 13 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 269 (accept_3_2 10 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 269 (accept_3_2 7 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 269 (accept_3_2 4 74 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2
  74 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 269 (accept_3_2 1 74 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 269 (allA_of_3_0 73 73 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 269 (allA_succ_of_accept 71 72 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 269 (accept_3_2 70 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 269 (accept_3_2 67 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 269 (Polychromatic418967fa.accept_19_9_15_3_1_12536 66 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 269
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 65 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 269 (accept_3_2 64 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 269 (accept_3_2 61 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 269
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 59 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 269 (accept_3_2 58 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 269 (accept_3_2 55 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 269
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 53 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 269 (accept_3_2 52 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 269 (accept_3_2 49 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 269 (accept_3_2 46 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 269 (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 269 (accept_3_2 43 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 72 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 269 (accept_3_2 40 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 269 (Polychromatic418967fa.accept_27_11_18_26_1_12687 38 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 269 (accept_3_2 37 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 269
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 35 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 269 (accept_3_2 34 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 269 (accept_3_2 31 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 72 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 269 (accept_3_2 28 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 269 (accept_3_2 25 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 269
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 269 (accept_3_2 22 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 269 (accept_3_2 19 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 269 (Polychromatic418967fa.accept_17_1_4_14_1_8058 18 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 269 (accept_3_2 16 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 269 (Polychromatic418967fa.accept_21_14_9_17_1_1712 14 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 269 (accept_3_2 13 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 269
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 269 (accept_3_2 10 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 269 (accept_3_2 7 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 269 (accept_3_2 4 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 72 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 269 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 269 (accept_3_2 1 72 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 269 (allA_succ_of_accept 70 71 269 (accept_3_2 70 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 69 71 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 269 (accept_3_2 67 71 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 269 (accept_3_2 64 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 269 (accept_3_2 61 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 269
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 59 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 269 (accept_3_2 58 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 269 (Polychromatic418967fa.accept_15_12_11_14_1_3464 57 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 269 (accept_3_2 55 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 269 (accept_3_2 52 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 269 (accept_3_2 49 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 269 (accept_3_2 46 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 269 (accept_3_2 43 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 269
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 269 (accept_3_2 40 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 269 (accept_3_2 37 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 269 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 269 (accept_3_2 34 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 269 (accept_3_2 31 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 269
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 269 (accept_3_2 28 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 269 (accept_3_2 25 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 269 (Polychromatic418967fa.accept_19_5_14_3_1_4187 24 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 269 (accept_3_2 22 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 269 (Polychromatic418967fa.accept_23_21_2_16_1_16403 21 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 269 (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 269 (accept_3_2 19 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 269
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 269 (accept_3_2 16 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 269 (accept_3_2 13 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 269 (accept_3_2 10 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 269 (accept_3_2 7 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 269 (accept_3_2 4 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 71 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 269 (accept_3_2 1 71 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 269 (allA_of_3_0 70 70 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 269
  (allA_succ_of_accept 68 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 269 (accept_3_2 67 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 65
  69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 269 (accept_3_2 64 69
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 269
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 269 (accept_3_2 61 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 59
  69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 269 (accept_3_2 58 69
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 269
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 269 (accept_3_2 55 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 269 (Polychromatic418967fa.accept_21_12_6_17_1_12037 54 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 269 (accept_3_2 52 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 269 (accept_3_2 49 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 269 (accept_3_2 46 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 269 (accept_3_2 43 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 269 (accept_3_2 40 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 269 (accept_3_2 37 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 269
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 269 (accept_3_2 34 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 269 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 269 (accept_3_2 31 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 269 (accept_3_2 28 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 269 (accept_3_2 25 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 269 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 269 (accept_3_2 22 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 269 (accept_3_2 19 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 269
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 269 (accept_3_2 16 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 269 (accept_3_2 13 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 269 (accept_3_2 10 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 269 (accept_3_2 7 69 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 69 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 269 (accept_3_2 4 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 269 (accept_3_2 1 69 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 269
  (allA_succ_of_accept 67 68 269 (accept_3_2 67 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 269 (accept_3_2 64 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 269 (accept_3_2 61 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 269 (Polychromatic418967fa.accept_13_7_3_9_1_1142 59 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 269 (accept_3_2 58 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 269 (accept_3_2 55 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 269 (Polychromatic418967fa.accept_21_11_5_17_1_760 53 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 269 (accept_3_2 52 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 269 (accept_3_2 49 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 269 (accept_3_2 46 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 269 (accept_3_2 43 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 269 (accept_3_2 40 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 269 (accept_3_2 37 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 269 (accept_3_2 34 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 269
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 32 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 269 (accept_3_2 31 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 269 (accept_3_2 28 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 269 (accept_3_2 25 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 269 (accept_3_2 22 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 269 (accept_3_2 19 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 269 (accept_3_2 16 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 269 (accept_3_2 13 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 269 (accept_3_2 10 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 269 (accept_3_2 7 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 68 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 269 (accept_3_2 4 68 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 269 (accept_3_2 1 68 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 269 (allA_of_3_0 67 67 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 269 (allA_succ_of_accept 65 66 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 269 (accept_3_2 64 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 269 (Polychromatic418967fa.accept_13_10_1_9_1_3380 62 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 269 (accept_3_2 61 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 269 (accept_3_2 58 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 57 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 269 (accept_3_2 55 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 269 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 269
  (Polychromatic418967fa.accept_10_3_6_9_1_779 53 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 269 (accept_3_2 52 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 269 (accept_3_2 49 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 269 (accept_3_2 46 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 44 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 269 (accept_3_2 43 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 269 (accept_3_2 40 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 269 (accept_3_2 37 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 269 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 269 (accept_3_2 34 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 269 (accept_3_2 31 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 269 (Polychromatic418967fa.accept_19_11_9_3_1_4167 30 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 269 (accept_3_2 28 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 269 (Polychromatic418967fa.accept_25_1_16_19_1_14714 26 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 269 (accept_3_2 25 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 269 (accept_3_2 22 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 269 (accept_3_2 19 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 269
  (Polychromatic418967fa.accept_20_17_6_9_1_6434 17 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 269 (accept_3_2 16 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 269 (accept_3_2 13 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 269 (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 66 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 269 (accept_3_2 10 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 269 (accept_3_2 7 66 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 269 (accept_3_2 4 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 66 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 269 (accept_3_2 1 66 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 269
  (allA_succ_of_accept 64 65 269 (accept_3_2 64 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 269 (Polychromatic418967fa.accept_19_6_8_3_1_11219 63 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 269 (accept_3_2 61 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 269 (accept_3_2 58 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 269 (accept_3_2 55 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 269
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 269 (accept_3_2 52 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 269 (accept_3_2 49 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 269 (accept_3_2 46 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 269 (Polychromatic418967fa.accept_21_3_2_17_1_7432 45 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 269 (accept_3_2 43 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 269 (accept_3_2 40 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 269 (Polychromatic418967fa.accept_15_8_5_14_1_986 38 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 269 (accept_3_2 37 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 269
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 269 (accept_3_2 34 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 269 (accept_3_2 31 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 269 (accept_3_2 28 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 269 (accept_3_2 25 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 269 (accept_3_2 22 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 269 (accept_3_2 19 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 269 (Polychromatic418967fa.accept_25_18_15_19_1_16402 18 65 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 269
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 269 (accept_3_2 16 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 269 (accept_3_2 13 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 269
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 269 (accept_3_2 10 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 269 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 269 (accept_3_2 7 65 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 269 (accept_3_2 4 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 65 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 269 (accept_3_2 1 65 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 269
  (allA_of_3_0 64 64 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 269 (allA_succ_of_accept 62 63 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 269 (accept_3_2 61 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 269 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 269 (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 269 (accept_3_2 58 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 63 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 269 (accept_3_2 55 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 269 (accept_3_2 52 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 269 (Polychromatic418967fa.accept_16_3_15_13_1_2825 51 63
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 269 (accept_3_2 49 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 269 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 269 (accept_3_2 46 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 269 (accept_3_2 43 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 41 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 269 (accept_3_2 40 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 269 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 269 (accept_3_2 37 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 269 (accept_3_2 34 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 269 (accept_3_2 31 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 269 (Polychromatic418967fa.accept_23_6_17_16_1_16401 29 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 269 (accept_3_2 28 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 269 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 63
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 269 (accept_3_2 25 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 269 (Polychromatic418967fa.accept_19_4_6_3_1_15078 23 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 269 (accept_3_2 22 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 269 (accept_3_2 19 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 269 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 269 (accept_3_2 16 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 269 (accept_3_2 13 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 269 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 269 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 269 (accept_3_2 10 63 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 269 (accept_3_2 7 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 269 (Polychromatic418967fa.accept_19_5_6_3_1_5578 5 63 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 269 (accept_3_2 4 63 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 269 (accept_3_2 1 63 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 269 (allA_succ_of_accept 61 62 269
  (accept_3_2 61 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 269 (accept_3_2 58 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 269 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 269 (accept_3_2 55
  62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 269
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 54 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 269 (accept_3_2 52 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693
  50 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 269 (accept_3_2 49
  62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 269
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 48 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 269 (accept_3_2 46 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 269 (accept_3_2 43 62
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 269
  (Polychromatic418967fa.accept_11_9_7_5_1_749 42 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 41 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 269 (accept_3_2 40 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 269
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 269 (accept_3_2 37 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 269 (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 269 (accept_3_2 34 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 269 (accept_3_2 31 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 269 (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 269 (accept_3_2 28 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 269
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 62 269 (accept_3_2 25 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 62 269 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 62 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 269 (accept_3_2 22 62 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 269
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 269 (accept_3_2 19 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 269 (accept_3_2 16 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 269
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 269 (accept_3_2 13 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 269 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 269 (accept_3_2 10 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 269 (accept_3_2 7 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  269 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 62 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 269 (accept_3_2 4 62 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 269 (accept_3_2 1 62 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 269 (allA_of_3_0 61 61 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 269 (allA_succ_of_accept 59 60 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 269 (accept_3_2 58 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 269 (accept_3_2 55 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 269 (Polychromatic418967fa.accept_22_10_16_5_1_14917 54 60 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 269
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 269 (accept_3_2 52 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 269 (accept_3_2 49 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 269 (accept_3_2 46 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 269 (Polychromatic418967fa.accept_21_3_18_17_1_12031 45 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 269 (Polychromatic418967fa.accept_23_21_14_16_1_13284 44 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 269 (accept_3_2 43 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 269 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 60 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 269 (accept_3_2 40 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 269 (accept_3_2 37 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 269
  (Polychromatic418967fa.accept_14_7_4_3_1_488 35 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 269 (accept_3_2 34 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 269 (accept_3_2 31 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 269 (accept_3_2 28 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 269 (Polychromatic418967fa.accept_16_10_12_13_1_4950 26 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 269 (accept_3_2 25 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 60
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 269 (accept_3_2 22 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 269 (accept_3_2 19 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 269 (Polychromatic418967fa.accept_22_18_16_5_1_5387 18 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 269 (accept_3_2 16 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 269 (accept_3_2 13 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 269 (accept_3_2 10 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 269 (accept_3_2 7 60 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 269 (accept_3_2 4 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 269 (accept_3_2 1 60 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 269
  (allA_succ_of_accept 58 59 269 (accept_3_2 58 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 269 (accept_3_2 55 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 269
  (Polychromatic418967fa.accept_20_13_19_9_1_10976 53 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 59 269 (accept_3_2 52 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 59 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 269 (accept_3_2 49 59 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48
  59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 269 (accept_3_2 46 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 269 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 269 (accept_3_2 43 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 269
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 269 (accept_3_2 40 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 269 (accept_3_2 37 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 269 (Polychromatic418967fa.accept_19_17_2_3_1_4190 36 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 269
  (Polychromatic418967fa.accept_19_16_2_3_1_5479 35 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 269 (accept_3_2 34 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 269 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 269 (accept_3_2 31 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 269 (accept_3_2 28 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 269 (Polychromatic418967fa.accept_28_27_3_17_1_16400 27 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 269 (accept_3_2 25 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 269
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 23 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 269 (accept_3_2 22 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 269 (accept_3_2 19 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 269
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 269 (accept_3_2 16 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 269 (accept_3_2 13 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 269 (accept_3_2 10 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 269 (Polychromatic418967fa.accept_22_9_15_5_1_10413 9 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 269 (accept_3_2 7 59 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 269
  (Polychromatic418967fa.accept_19_5_2_3_1_5527 5 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 269 (accept_3_2 4 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 269 (accept_3_2 1 59 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 269 (allA_of_3_0
  58 58 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 269 (allA_succ_of_accept 56 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 269 (accept_3_2 55 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 269 (accept_3_2 52 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 269 (accept_3_2 49 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 269 (accept_3_2 46 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 269 (Polychromatic418967fa.accept_21_3_15_17_1_7487 45 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 269 (accept_3_2 43 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 269 (accept_3_2 40 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 269 (accept_3_2 37 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 269 (Polychromatic418967fa.accept_21_14_15_17_1_2972 35 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 269 (accept_3_2 34 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 269 (accept_3_2 31 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 269 (accept_3_2 28 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 269 (accept_3_2 25 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 269 (accept_3_2 22 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 269 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 269 (accept_3_2 19 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 269 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 269 (accept_3_2 16 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 269 (accept_3_2 13 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 269 (accept_3_2 10 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 269 (accept_3_2 7 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 269 (accept_3_2 4 57 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 57 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 269 (accept_3_2 1 57 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 269 (allA_succ_of_accept 55 56 269 (accept_3_2 55 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 269 (Polychromatic418967fa.accept_19_16_18_3_1_15081 54 56 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 56 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 269 (accept_3_2 52 56 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 269 (accept_3_2 49 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 269 (Polychromatic418967fa.accept_13_8_4_9_1_1145 47 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 269 (accept_3_2 46 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 269
  (Polychromatic418967fa.accept_13_5_4_9_1_601 44 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 269 (accept_3_2 43 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 269 (accept_3_2 40 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 269 (accept_3_2 37 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 269 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 269 (accept_3_2 34 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 269 (accept_3_2 31 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 269 (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 269 (accept_3_2 28 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 269 (accept_3_2 25 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 269 (accept_3_2 22 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 269
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 269 (accept_3_2 19 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 269 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 269 (accept_3_2 16 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 269 (accept_3_2 13 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 269 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 269 (accept_3_2 10 56 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 269
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 8 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 269 (accept_3_2 7 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 269 (accept_3_2 4 56 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 269 (accept_3_2 1 56 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 269 (allA_of_3_0 55 55 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 269
  (allA_succ_of_accept 53 54 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 269 (accept_3_2 52 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 269 (accept_3_2 49 54
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 269 (accept_3_2 46 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 269 (accept_3_2 43 54
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 269
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 269 (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 269 (accept_3_2 40 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 269 (accept_3_2 37
  54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 269 (accept_3_2 34 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188
  32 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 269 (accept_3_2 31
  54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 269 (accept_3_2 28 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202
  26 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 269 (accept_3_2 25
  54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 269
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 269 (accept_3_2 22 54 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 54 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 269
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 269 (accept_3_2 19 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 269 (accept_3_2 16 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 269
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 269 (accept_3_2 13 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 269 (accept_3_2 10 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 269 (accept_3_2 7 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  269 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 269 (accept_3_2 4 54 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 269 (accept_3_2 1 54 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 269 (allA_succ_of_accept 52 53 269 (accept_3_2
  52 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 269
  (Polychromatic418967fa.accept_11_7_9_5_1_338 51 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 269 (accept_3_2 49 53 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  47 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 269 (accept_3_2 46
  53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 269
  (Polychromatic418967fa.accept_13_6_1_9_1_619 45 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 53 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 269 (accept_3_2 43 53 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 269 (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 269 (accept_3_2 40 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 39 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 269 (Polychromatic418967fa.accept_22_16_9_5_1_10441 38 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 269 (accept_3_2 37 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 269
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 269 (accept_3_2 34 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 269 (Polychromatic418967fa.accept_13_6_1_9_1_619 32 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 269 (accept_3_2 31 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 269 (Polychromatic418967fa.accept_20_10_13_9_1_6429 30 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 269 (accept_3_2 28 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 269 (accept_3_2 25 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 269
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 269 (accept_3_2 22 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 269 (accept_3_2 19 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 269
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 269 (accept_3_2 16 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 269 (accept_3_2 13 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 269 (Polychromatic418967fa.accept_19_12_15_3_1_8433 12 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 269
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 269 (accept_3_2 10 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 269 (accept_3_2 7 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 269
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 269 (accept_3_2 4 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  269 (Polychromatic418967fa.accept_17_3_2_14_1_6714 3 53 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 269 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 269 (accept_3_2 1 53 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 269))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 269
  (allA_of_3_0 52 52 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 269 (allA_succ_of_accept 50 51 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 269 (accept_3_2 49 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 269 (accept_3_2 46 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 269 (accept_3_2 43 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 269 (accept_3_2 40 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 269 (accept_3_2 37 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 269 (accept_3_2 34 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 269 (accept_3_2 31 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 269 (accept_3_2 28 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 269 (accept_3_2 25 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 269 (accept_3_2 22 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 269 (accept_3_2 19 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 269 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 269 (accept_3_2 16 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 269 (accept_3_2 13 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 269 (accept_3_2 10 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 269 (accept_3_2 7 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 269 (accept_3_2 4 51 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 269 (accept_3_2 1 51 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 269)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 269 (allA_succ_of_accept 49 50 269 (accept_3_2 49 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 269 (accept_3_2 46 50 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 269 (accept_3_2 43 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 41 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 269 (accept_3_2 40 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 269 (accept_3_2 37 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 269 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 269 (accept_3_2 34 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 269 (accept_3_2 31 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 269 (accept_3_2 28 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 269 (accept_3_2 25 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 269 (accept_3_2 22 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 269 (accept_3_2 19 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 269 (accept_3_2 16 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 269
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 269 (accept_3_2 13 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 269 (accept_3_2 10 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 269 (accept_3_2 7 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 269 (accept_3_2 4 50 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  50 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 269 (accept_3_2 1 50 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 269)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 269 (allA_of_3_0 49 49 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 269 (allA_succ_of_accept 47 48
  269 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 269 (accept_3_2 46 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 269 (Polychromatic418967fa.accept_18_9_12_17_1_6060 45 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 269 (accept_3_2 43 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 269 (accept_3_2 40 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 269 (accept_3_2 37 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 269 (Polychromatic418967fa.accept_21_15_6_17_1_7466 36 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 269
  (Polychromatic418967fa.accept_25_10_23_19_1_16399 35 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 48 269 (accept_3_2 34 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 269 (accept_3_2 31 48 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 269 (accept_3_2 28 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 269 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 269 (accept_3_2 25 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 269 (accept_3_2 22 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 269 (accept_3_2 19 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 269
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 269 (accept_3_2 16 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 269 (accept_3_2 13 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 269 (Polychromatic418967fa.accept_19_12_10_3_1_5503 12 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 269 (accept_3_2 10 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 269 (Polychromatic418967fa.accept_23_8_2_16_1_14782 8 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 269 (accept_3_2 7 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 269 (accept_3_2 4 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  269 (Polychromatic418967fa.accept_25_3_23_19_1_16398 3 48 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 269 (accept_3_2 1 48 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 269)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 269
  (allA_succ_of_accept 46 47 269 (accept_3_2 46 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 269 (Polychromatic418967fa.accept_20_5_7_9_1_6425 45 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 269 (accept_3_2 43 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 269 (accept_3_2 40 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 269 (accept_3_2 37 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 269
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 269 (accept_3_2 34 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 269 (accept_3_2 31 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 269 (accept_3_2 28 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 269 (accept_3_2 25 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 269 (accept_3_2 22 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 269 (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 269 (accept_3_2 19 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 269
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 269 (accept_3_2 16 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 269 (accept_3_2 13 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 269
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 269 (accept_3_2 10 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 269 (accept_3_2 7 47 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 269 (accept_3_2 4 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 269 (accept_3_2 1 47 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 269))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 269 (allA_of_3_0 46 46 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 269 (allA_succ_of_accept 44 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 269 (accept_3_2 43 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 269 (accept_3_2 40 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 269 (accept_3_2 37 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 269 (Polychromatic418967fa.accept_20_15_5_9_1_3479 35 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 269 (accept_3_2 34 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 269 (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 45 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 269 (accept_3_2 31 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 269 (accept_3_2 28 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 269 (accept_3_2 25 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 269 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 269 (accept_3_2 22 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 269 (accept_3_2 19 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 269 (Polychromatic418967fa.accept_21_18_3_17_1_13577 18 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 269 (accept_3_2 16 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 269 (accept_3_2 13 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 269 (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 269 (accept_3_2 10 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 269 (Polychromatic418967fa.accept_21_9_3_17_1_4365 9 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 269 (accept_3_2 7 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 45 269 (Polychromatic418967fa.accept_19_5_7_3_1_6990 5 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 269 (accept_3_2 4 45 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 269 (accept_3_2 1 45 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  269))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 269 (allA_succ_of_accept 43 44 269 (accept_3_2 43 44
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 269
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 269 (accept_3_2 40 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 269 (accept_3_2 37
  44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 269 (accept_3_2 34 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 269
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 32 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 269 (accept_3_2 31 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 269 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 269 (accept_3_2 28 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 269 (accept_3_2 25 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 269 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 269 (accept_3_2 22 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 269 (accept_3_2 19 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 269 (accept_3_2 16 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 269 (accept_3_2 13 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 269 (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 44 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 269 (accept_3_2 10 44 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 269 (accept_3_2 7 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 269 (accept_3_2 4 44 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  44 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 269 (accept_3_2 1 44 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 269)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  269 (allA_of_3_0 43 43 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 269 (allA_succ_of_accept 41 42 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 269 (accept_3_2 40 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 269 (accept_3_2 37 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 269 (Polychromatic418967fa.accept_24_12_18_5_1_16397 36 42 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 269 (accept_3_2 34 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 269 (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 269 (accept_3_2 31 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 269 (accept_3_2 28 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 269 (accept_3_2 25 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 42
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 269 (accept_3_2 22 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 269 (accept_3_2 19 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 269 (accept_3_2 16 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 269 (accept_3_2 13 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 269 (accept_3_2 10 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 269 (accept_3_2 7 42 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 42 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 269 (accept_3_2 4 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 269 (accept_3_2 1 42 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 269)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 269 (allA_succ_of_accept 40 41
  269 (accept_3_2 40 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 269 (accept_3_2 37 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 269 (Polychromatic418967fa.accept_10_5_1_9_1_791
  35 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 269 (accept_3_2 34
  41 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 269
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 269 (accept_3_2 31 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 269 (accept_3_2 28 41
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 269
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 269 (accept_3_2 25 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 269 (accept_3_2 22 41
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 269 (Polychromatic418967fa.accept_9_3_5_8_1_99
  21 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 269
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 269 (accept_3_2 19 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 269 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 41 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 269 (accept_3_2 16 41 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 269
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 269 (accept_3_2 13 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 269 (accept_3_2 10 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 269
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 269 (accept_3_2 7 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 269 (accept_3_2 4 41 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  41 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 269 (accept_3_2 1 41 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 269))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 269
  (allA_of_3_0 40 40 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 269 (allA_succ_of_accept 38 39 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 269 (accept_3_2 37 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 269 (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 269 (accept_3_2 34 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 269 (accept_3_2 31 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 269 (accept_3_2 28 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 269 (accept_3_2 25 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 269 (accept_3_2 22 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 269 (accept_3_2 19 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 269 (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 269 (accept_3_2 16 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 269 (accept_3_2 13 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 269 (accept_3_2 10 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 269 (accept_3_2 7 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 269 (accept_3_2 4 39 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 269 (Polychromatic418967fa.accept_20_3_19_9_1_4976 3 39 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 269 (accept_3_2 1 39 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 269))))))))))))))))))))))))))))))))))))))) (allB_succ 38 269
  (allA_succ_of_accept 37 38 269 (accept_3_2 37 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 269 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 269 (accept_3_2 34 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 269 (accept_3_2 31 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 269 (accept_3_2 28 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 269
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 26 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 269 (accept_3_2 25 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 269 (accept_3_2 22 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 269 (accept_3_2 19 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 269 (Polychromatic418967fa.accept_17_1_4_14_1_8058 18 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 269 (accept_3_2 16 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 269 (accept_3_2 13 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 269 (accept_3_2 10 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 269 (accept_3_2 7 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 269 (accept_3_2 4 38 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 269
  (Polychromatic418967fa.accept_27_2_11_26_1_16396 2 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 269 (accept_3_2 1 38 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  269)))))))))))))))))))))))))))))))))))))) (allB_succ 37 269 (allA_of_3_0 37 37 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 269 (allA_succ_of_accept 35 36 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 269 (accept_3_2 34 36 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 269 (accept_3_2 31 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 269 (Polychromatic418967fa.accept_21_8_15_17_1_4382 29 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 269 (accept_3_2 28 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 36 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 269 (accept_3_2 25 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 269 (accept_3_2 22 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 269 (Polychromatic418967fa.accept_19_2_17_3_1_11224 21 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 269
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 269 (accept_3_2 19 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 269 (accept_3_2 16 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 269
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 269 (accept_3_2 13 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  36 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 36 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 269 (accept_3_2 10 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 269
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 269 (accept_3_2 7 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  269 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 36 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 269 (accept_3_2 4 36 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 36 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 269 (accept_3_2 1 36 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  269)))))))))))))))))))))))))))))))))))) (allB_succ 35 269 (allA_succ_of_accept 34 35 269 (accept_3_2 34 35 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 269 (Polychromatic418967fa.accept_16_1_3_13_1_2785
  33 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 269
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 32 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 269 (accept_3_2 31 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 269 (Polychromatic418967fa.accept_21_8_14_17_1_2968 29 35 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 269 (accept_3_2 28 35 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 269 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 35
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 269 (accept_3_2 25 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 269 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 269 (accept_3_2 22 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 35 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 269
  (Polychromatic418967fa.accept_19_1_16_3_1_11223 20 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 269 (accept_3_2 19 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 269 (accept_3_2 16 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 269 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 35 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 269 (accept_3_2 13 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 269 (Polychromatic418967fa.accept_25_12_10_19_1_16395 12 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 269 (accept_3_2 10 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 269 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 35 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 269
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 269 (accept_3_2 7 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 269 (Polychromatic418967fa.accept_19_5_16_3_1_1820 5 35 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 269 (accept_3_2 4 35 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 269 (Polychromatic418967fa.accept_20_3_15_9_1_6456 3 35 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 269 (accept_3_2 1 35 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 269))))))))))))))))))))))))))))))))))) (allB_succ 34 269
  (allA_of_3_0 34 34 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 269 (allA_succ_of_accept 32 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 269 (accept_3_2 31 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 269 (accept_3_2 28 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 269 (accept_3_2 25 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 269 (accept_3_2 22 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 269 (accept_3_2 19 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 269 (Polychromatic418967fa.accept_19_18_14_3_1_8427 18 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 269 (accept_3_2 16 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 269 (accept_3_2 13 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 269 (accept_3_2 10 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 269 (accept_3_2 7 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 269 (accept_3_2 4 33 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 269 (accept_3_2 1 33 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  269))))))))))))))))))))))))))))))))) (allB_succ 32 269 (allA_succ_of_accept 31 32 269 (accept_3_2 31 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 269 (accept_3_2 28 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  32 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 269 (accept_3_2 25 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 269
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 269 (accept_3_2 22 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 269 (accept_3_2 19 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 269 (accept_3_2 16 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 269 (accept_3_2 13 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 269 (accept_3_2 10 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 269 (accept_3_2 7 32 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 269
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 269 (accept_3_2 4 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 269 (accept_3_2 1 32 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 269)))))))))))))))))))))))))))))))) (allB_succ 31 269 (allA_of_3_0 31 31 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 269 (allA_succ_of_accept 29 30 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 269 (accept_3_2 28 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 269 (accept_3_2 25 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 269 (accept_3_2 22 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 269 (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 269 (accept_3_2 19 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 269 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 30 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 269
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 269 (accept_3_2 16 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 269 (accept_3_2 13 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 269 (accept_3_2 10 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 269 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 269 (accept_3_2 7 30 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 269 (accept_3_2 4 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 269 (accept_3_2 1 30 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 269)))))))))))))))))))))))))))))) (allB_succ 29 269 (allA_succ_of_accept 28 29 269
  (accept_3_2 28 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 269
  (Polychromatic418967fa.accept_28_27_1_17_1_16394 27 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 269 (accept_3_2 25 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 269 (accept_3_2 22 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 269 (accept_3_2 19 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 269
  (Polychromatic418967fa.accept_23_17_6_16_1_16393 17 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 29 269 (accept_3_2 16 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 29 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 269 (accept_3_2 13 29 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 269 (accept_3_2 10 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 269 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 269 (accept_3_2 7 29 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 269 (accept_3_2 4 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 269 (accept_3_2 1 29 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 269))))))))))))))))))))))))))))) (allB_succ 28 269 (allA_of_3_0 28 28 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 269 (allA_succ_of_accept 26 27 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 269 (accept_3_2 25 27 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 269 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  24 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 269 (accept_3_2 22 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 269 (accept_3_2 19 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 269
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 269 (accept_3_2 16 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 269 (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 269 (accept_3_2 13 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 269 (accept_3_2 10 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 269 (accept_3_2 7 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 269
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 269 (accept_3_2 4 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  269 (Polychromatic418967fa.accept_25_3_2_19_1_16392 3 27 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 27 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 269 (accept_3_2 1 27 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 27 269))))))))))))))))))))))))))) (allB_succ 26 269 (allA_succ_of_accept 25 26 269
  (accept_3_2 25 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 269
  (Polychromatic418967fa.accept_19_5_7_3_1_6990 24 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 269 (accept_3_2 22 26 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 269 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 269 (accept_3_2 19
  26 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 269
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 269 (Polychromatic418967fa.accept_20_17_6_9_1_6434 17 26 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 269 (accept_3_2 16 26 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 269
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 26 269 (accept_3_2 13 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 26 269 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 26 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 269 (accept_3_2 10 26 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 269 (accept_3_2 7 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  269 (Polychromatic418967fa.accept_19_6_7_3_1_1733 6 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 26 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 26 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 269 (accept_3_2 4 26 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 269 (accept_3_2 1 26 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  269)))))))))))))))))))))))))) (allB_succ 25 269 (allA_of_3_0 25 25 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 269 (allA_succ_of_accept 23 24 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 269 (accept_3_2 22 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 269 (accept_3_2 19 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 269 (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 269 (accept_3_2 16 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 24 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 269 (accept_3_2 13 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 269 (accept_3_2 10 24 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 269 (Polychromatic418967fa.accept_21_9_3_17_1_4365 9 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 269 (accept_3_2 7 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 269 (accept_3_2 4 24 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 269 (accept_3_2 1 24 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  269)))))))))))))))))))))))) (allB_succ 23 269 (allA_succ_of_accept 22 23 269 (accept_3_2 22 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 269 (accept_3_2 19 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 269 (accept_3_2 16 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 269 (accept_3_2 13 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 269 (accept_3_2 10 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 23 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 269 (accept_3_2 7 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 269 (accept_3_2 4 23 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 269 (accept_3_2 1 23 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 269))))))))))))))))))))))) (allB_succ 22 269 (allA_of_3_0 22 22
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 269 (allA_succ_of_accept 20 21 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 269 (accept_3_2 19 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 21 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 269 (accept_3_2 16 21 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 269 (accept_3_2 13 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 269 (accept_3_2 10 21 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 269 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 21 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 269 (accept_3_2 7 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 269 (accept_3_2 4 21 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 269 (accept_3_2 1 21 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 269))))))))))))))))))))) (allB_succ 20 269 (allA_succ_of_accept
  19 20 269 (accept_3_2 19 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 269 (accept_3_2 16 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 269 (accept_3_2 13 20
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 269
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 269 (accept_3_2 10 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 8
  20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 269 (accept_3_2 7 20 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 269 (accept_3_2 4 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 269 (accept_3_2 1 20 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 269)))))))))))))))))))) (allB_succ 19 269 (allA_of_3_0 19 19 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 269 (allA_succ_of_accept 17 18 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 18 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 269 (accept_3_2 16 18 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 269 (accept_3_2 13 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 269 (Polychromatic418967fa.accept_22_12_18_5_1_16391 12 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 269 (accept_3_2 10 18 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 18 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 269 (accept_3_2 7 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 269 (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 18 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 269 (accept_3_2 4 18 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 2
  18 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 269 (accept_3_2 1 18 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 269)))))))))))))))))) (allB_succ 17 269 (allA_succ_of_accept 16
  17 269 (accept_3_2 16 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 269
  (Polychromatic418967fa.accept_19_15_17_3_1_13760 15 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 269 (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 17 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 269 (accept_3_2 13 17 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 269
  (Polychromatic418967fa.accept_22_11_17_5_1_16390 11 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 17 269 (accept_3_2 10 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 17 269 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 17 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 17 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 269 (accept_3_2 7 17 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 269 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6
  17 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 269
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 269 (accept_3_2 4 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 17 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 17 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 269 (accept_3_2 1 17 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 269))))))))))))))))) (allB_succ 16 269 (allA_of_3_0 16 16 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 15 269 (allA_succ_of_accept 14 15 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 269 (accept_3_2 13 15 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  15 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 269 (accept_3_2 10 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 269 (accept_3_2 7 15 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 269 (accept_3_2 4 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 269 (accept_3_2 1 15 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 269))))))))))))))) (allB_succ 14 269 (allA_succ_of_accept 13 14 269 (accept_3_2 13 14 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  14 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 269 (accept_3_2 10 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 14 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 269 (accept_3_2 7 14 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 269
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 269 (accept_3_2 4 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 269 (accept_3_2 1 14 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 269)))))))))))))) (allB_succ 13 269 (allA_of_3_0 13 13 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 269 (allA_succ_of_accept 11 12 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 269 (accept_3_2 10 12 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 269 (accept_3_2 7 12 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 12 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 269 (accept_3_2 4 12 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 12 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 269 (accept_3_2 1 12 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 269)))))))))))) (allB_succ 11 269 (allA_succ_of_accept 10 11 269
  (accept_3_2 10 11 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 269
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 9 11 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 269 (accept_3_2 7 11 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  11 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 269 (accept_3_2 4 11 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  11 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 269 (accept_3_2 1 11 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  269))))))))))) (allB_succ 10 269 (allA_of_3_0 10 10 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 269
  (allA_succ_of_accept 8 9 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 269 (accept_3_2 7 9 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 269 (accept_3_2 4 9 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 269 (accept_3_2 1 9 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 269)))))))))
  (allB_succ 8 269 (allA_succ_of_accept 7 8 269 (accept_3_2 7 8 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 269 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 8 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 269 (accept_3_2 4 8 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 269 (accept_3_2 1 8 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 269))))))))
  (allB_succ 7 269 (allA_of_3_0 7 7 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 269 (allA_succ_of_accept 5
  6 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 269 (accept_3_2 4 6 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 269 (accept_3_2 1 6 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 269)))))) (allB_succ 5 269 (allA_succ_of_accept 4 5 269 (accept_3_2 4 5 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 269 (accept_3_2 1 5 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 269)))))
  (allB_succ 4 269 (allA_of_3_0 4 4 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 269 (allA_succ_of_accept 2
  3 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 269 (accept_3_2 1 3 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 269)))
  (allB_succ 2 269 (allA_succ_of_accept 1 2 269 (accept_3_2 1 2 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  269)) (allB_two
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


