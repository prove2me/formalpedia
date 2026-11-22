-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch287_Segment000
-- name    : Polychromatic418967fa_Branch287_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:54:06.700919+00:00
-- url     : https://prove2.me/theorems/40d70440-efb6-481b-8778-e17e0ca8e17a
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

def Polychromatic418967fa.branch_287_segment_000 : allB 123 287 :=
  allB_succ 122 287 (allA_succ_of_accept 121 122 287 (accept_3_2 121 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 122
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 287 (accept_3_2 118 122
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 116 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 287 (accept_3_2 115 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 287 (accept_3_2 112 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 287 (accept_3_2 109 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 108 122
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 287
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 107 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 287 (accept_3_2 106 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 104 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 287 (accept_3_2 103 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 122
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 287 (accept_3_2 100 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 287 (Polychromatic418967fa.accept_20_18_2_7_1_6285 98 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 287 (accept_3_2 97 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 95 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 287 (accept_3_2 94 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 287 (accept_3_2 91 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 90 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 287 (accept_3_2 88 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 86 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 287 (accept_3_2 85 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 287 (accept_3_2 82 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 287 (accept_3_2 79 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 287 (accept_3_2 76 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 287 (accept_3_2 73 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 287 (Polychromatic418967fa.accept_19_15_8_2_1_4110 72 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 287
  (Polychromatic418967fa.accept_13_6_5_1_1_834 71 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 287 (accept_3_2 70 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 287 (accept_3_2 67 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 287 (accept_3_2 64 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 62 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 287 (accept_3_2 61 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 122 287 (accept_3_2 58 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 287 (accept_3_2 55 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 122 287 (accept_3_2 52 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 122 287 (Polychromatic418967fa.accept_21_8_17_14_1_4156 50 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 287 (accept_3_2 49 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 122 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 122 287 (accept_3_2 46 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 122 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 287 (accept_3_2 43 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 122 287 (accept_3_2 40 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 287 (accept_3_2 37 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 287 (Polychromatic418967fa.accept_21_15_17_14_1_4191 36 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 287 (accept_3_2 34 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 287 (accept_3_2 31 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 287 (accept_3_2 28 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 287 (Polychromatic418967fa.accept_21_5_17_14_1_4178 26 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 287 (accept_3_2 25 122 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 287
  (Polychromatic418967fa.accept_21_2_17_14_1_5644 23 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 122 287 (accept_3_2 22 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 287 (accept_3_2 19 122 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 287
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 287 (accept_3_2 16 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 287 (Polychromatic418967fa.accept_10_4_2_7_1_373
  14 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 287 (accept_3_2 13
  122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 287 (accept_3_2 10 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  8 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 287 (accept_3_2 7
  122 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 122 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 287 (accept_3_2 4 122 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 122 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  122 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 287 (accept_3_2 1 122
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 287 (allA_of_3_0 121 121 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 287
  (allA_succ_of_accept 119 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 287 (accept_3_2 118 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 120 287 (Polychromatic418967fa.accept_18_9_12_17_1_6060 117 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 116 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 120 287 (accept_3_2 115 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 114 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 287 (accept_3_2 112 120
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 111 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 120 287 (accept_3_2 109 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 120 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 108 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 287
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 107 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 120 287 (accept_3_2 106 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 120 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 120
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 287 (accept_3_2 103 120
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 102 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 287 (accept_3_2 100 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 287 (Polychromatic418967fa.accept_14_1_8_7_1_1253 99 120
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 98 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 287 (accept_3_2 97 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 287 (accept_3_2 94 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 93 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 287 (accept_3_2 91 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 89 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 287 (accept_3_2 88 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 120 287 (accept_3_2 85 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 120 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 84 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 287 (accept_3_2 82 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 81 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 287
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 287 (accept_3_2 79 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 287 (accept_3_2 76 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 287 (accept_3_2 73 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 287 (accept_3_2 70 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 287 (accept_3_2 67 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 287 (Polychromatic418967fa.accept_21_3_15_14_1_5722 66 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 287 (accept_3_2 64 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 287
  (Polychromatic418967fa.accept_14_6_8_7_1_589 62 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 287 (accept_3_2 61 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 287 (accept_3_2 58 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 287 (accept_3_2 55 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 287 (accept_3_2 52 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 287 (accept_3_2 49 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 48 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 287 (accept_3_2 46 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 287 (accept_3_2 43 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 287 (accept_3_2 40 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 287 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 287 (accept_3_2 37 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 287 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 287 (accept_3_2 34 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 287 (accept_3_2 31 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 287 (accept_3_2 28 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 287 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 287
  (Polychromatic418967fa.accept_17_9_1_15_1_3156 26 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 287 (accept_3_2 25 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 287 (accept_3_2 22 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 287 (Polychromatic418967fa.accept_27_21_12_17_1_17629 21 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 287 (accept_3_2 19 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 287 (accept_3_2 16 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 287 (accept_3_2 13 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 287 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 287 (accept_3_2 10 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 287
  (Polychromatic418967fa.accept_19_8_6_2_1_11146 8 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 287 (accept_3_2 7 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 287 (accept_3_2 4 120 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 287 (Polychromatic418967fa.accept_17_3_1_15_1_6835 3 120 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 287 (accept_3_2 1 120 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 287 (allA_succ_of_accept 118 119 287 (accept_3_2 118 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 117 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 287
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 116 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 119 287 (accept_3_2 115 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 119 287 7 16 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 119 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 111 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 119 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 110 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 287 (accept_3_2 109 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 119 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 119 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 287
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 107 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 287 (accept_3_2 106 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  105 119 287 7 15 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 104 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 287 (accept_3_2 103 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 287
  (Polychromatic418967fa.accept_22_13_9_1_1_11605 101 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 119 287 (accept_3_2 100 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 119 287 (Polychromatic418967fa.accept_16_3_7_15_1_1130 99 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 119 287 7 14 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 119 287 (accept_3_2 97 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 287 (accept_3_2 94 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 92 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 119 287 7 13 17 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 119 287
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 119 287 (Polychromatic418967fa.accept_23_20_4_11_1_2963 89 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 287 (accept_3_2 88 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 287 (accept_3_2 85 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  119 287 7 12 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 119 287 (Polychromatic418967fa.accept_16_3_7_15_1_1130 83 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 287 (accept_3_2 82 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 119 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 287 (accept_3_2 79 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 119 287 7 11 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 119 287 (accept_3_2 76 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 74 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 287 (accept_3_2 73 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 287
  (Polychromatic418967fa.accept_10_2_9_7_1_720 72 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 119 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 119 287 7 10 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69
  119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 287 (accept_3_2 67 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 287 (accept_3_2 64 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 119 287 7 9 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 119 287 (Polychromatic418967fa.accept_10_2_9_7_1_720
  62 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 287 (accept_3_2 61
  119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 287 (accept_3_2 58 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 119 287 7 8 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 119 287 (accept_3_2 55 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 287
  (Polychromatic418967fa.accept_23_7_4_11_1_14489 53 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 119 287 (accept_3_2 52 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 119 287 7 7 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 119 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 287 (Polychromatic418967fa.accept_22_3_9_1_1_6771 47 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 287 (accept_3_2 46 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 287
  (Polychromatic418967fa.accept_29_15_3_26_1_17628 44 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 119 287 (accept_3_2 43 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 119 287 7 6 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 287 (accept_3_2 40 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118
  38 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 287 (accept_3_2 37
  119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 287
  (Polychromatic418967fa.accept_19_17_5_2_1_2843 36 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 119 287 7 5 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 119 287 (accept_3_2 34 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 287 (accept_3_2 31 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 287
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 287 7 4 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 287 (Polychromatic418967fa.accept_19_7_5_2_1_2842
  26 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 287 (accept_3_2 25
  119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 287 (accept_3_2 22 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 119 287 7 3 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 119 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 287 (accept_3_2 19 119 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 287
  (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 287 (accept_3_2 16 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 119 287 7 2 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 119 287 (accept_3_2 13 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 287 (accept_3_2 10 119
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 287
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 119 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 119 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 287 7 1 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 287 (accept_3_2 4 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 287 (accept_3_2 1 119 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 287 (allA_of_3_0 118 118 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 287
  (allA_succ_of_accept 116 117 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 287 (accept_3_2 115 117 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 287
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 113 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 117 287 (accept_3_2 112 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  110 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 287 (accept_3_2
  109 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 287
  (Polychromatic418967fa.accept_15_3_12_2_1_507 108 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 107 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 287 (accept_3_2 106 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 105 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 117 287 (accept_3_2 103 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 117 287 (Polychromatic418967fa.accept_19_6_3_2_1_4119 101 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 287 (accept_3_2 100 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 117 287 (accept_3_2 97 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 117 287 (Polychromatic418967fa.accept_14_12_5_7_1_2010 96 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 95 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 287 (accept_3_2 94 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 93 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 287 (accept_3_2 91 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 287 (Polychromatic418967fa.accept_15_14_12_2_1_3804 89 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 287 (accept_3_2 88 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 287 (accept_3_2 85 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 287 (Polychromatic418967fa.accept_16_4_5_15_1_5083 84 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 287 (accept_3_2 82 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 81 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 287 (accept_3_2 79 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 287 (Polychromatic418967fa.accept_19_1_3_2_1_11168 77 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 287 (accept_3_2 76 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 287 (accept_3_2 73 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 287 (Polychromatic418967fa.accept_21_8_12_14_1_10464 71 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 287 (accept_3_2 70 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 287 (Polychromatic418967fa.accept_18_15_9_17_1_6043 69 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 287 (accept_3_2 67 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 65 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 287 (accept_3_2 64 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 287 (accept_3_2 61 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 287 (Polychromatic418967fa.accept_21_18_12_14_1_11842 60 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 287 (Polychromatic418967fa.accept_15_14_12_2_1_3804 59 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 287 (accept_3_2 58 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 287
  (Polychromatic418967fa.accept_21_15_12_14_1_7232 57 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 287 (accept_3_2 55 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 287
  (Polychromatic418967fa.accept_21_11_12_14_1_5670 53 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 117 287 (accept_3_2 52 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 117 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 287 (accept_3_2 49 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 287 (Polychromatic418967fa.accept_15_3_12_2_1_507
  48 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 287
  (Polychromatic418967fa.accept_21_5_12_14_1_7241 47 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 117 287 (accept_3_2 46 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 117 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 45 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44
  117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 287 (accept_3_2 43
  117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 287 (Polychromatic418967fa.accept_31_10_24_8_1_17627 41 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 287 (accept_3_2 40 117 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 287 (accept_3_2 37 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 287 (accept_3_2 34 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 287 (accept_3_2 31 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 287 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 287 (accept_3_2 28 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 287 (accept_3_2 25 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 287 (Polychromatic418967fa.accept_19_5_3_2_1_2867 24 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 287 (accept_3_2 22 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 287 (accept_3_2 19 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 287 (accept_3_2 16 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 117
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 287 (accept_3_2 13 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 287 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 287 (Polychromatic418967fa.accept_19_11_3_2_1_12485 11 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 287 (accept_3_2 10 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 287 (accept_3_2 7 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 287 (accept_3_2 4 117 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 117 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 287 (accept_3_2 1 117 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 287 (allA_succ_of_accept 115 116 287 (accept_3_2 115 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 114 116 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 113 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 116 287 (accept_3_2 112 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 110 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 287 (accept_3_2 109 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 116 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 108
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 287 (accept_3_2 106 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 104 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 287 (accept_3_2 103 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 102
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 101 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 287 (accept_3_2 100 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 287 (accept_3_2 97 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 96 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 95 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 287 (accept_3_2 94 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 287 (Polychromatic418967fa.accept_16_12_4_15_1_5091 92 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 287 (accept_3_2 91 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 287 (Polychromatic418967fa.accept_21_6_11_14_1_11812 90
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 116 287 (accept_3_2 88 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 287 (accept_3_2 85 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 84 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 116 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 116 287 (accept_3_2 82 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 116 287 (Polychromatic418967fa.accept_13_2_12_1_1_343
  80 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 287 (accept_3_2 79
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 287
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 78 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 116 287 (Polychromatic418967fa.accept_18_5_8_17_1_3478 77 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 116 287 (accept_3_2 76 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 116 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 116 287 (accept_3_2 73 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 116 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 116 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 116 287 (accept_3_2 70 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 287
  (Polychromatic418967fa.accept_21_5_11_14_1_7219 68 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 116 287 (accept_3_2 67 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 116 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 287 (accept_3_2 64 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 116 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 287 (accept_3_2 61 116 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 116 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 287 (accept_3_2 58 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 287 (accept_3_2 55 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 287 (accept_3_2 52 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 287 (accept_3_2 49 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 287 (Polychromatic418967fa.accept_21_6_11_14_1_11812 48
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 287 (accept_3_2 46 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 287 (accept_3_2 43 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 287 (Polychromatic418967fa.accept_27_15_8_17_1_17626 42
  116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 287 (accept_3_2 40 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 287 (accept_3_2 37 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 287 (accept_3_2 34 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 287 (Polychromatic418967fa.accept_25_7_16_12_1_17625 32 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 287 (accept_3_2 31 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 287 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 287 (accept_3_2 28 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 287 (accept_3_2 25 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 287 (accept_3_2 22 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 287 (accept_3_2 19 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 287
  (Polychromatic418967fa.accept_14_3_4_7_1_175 17 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 287 (accept_3_2 16 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 287 (accept_3_2 13 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 287 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 287 (accept_3_2 10 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 287 (accept_3_2 7 116 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 116
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 287 (accept_3_2 4 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 287 (accept_3_2 1 116 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 287 (allA_of_3_0 115 115 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 287
  (allA_succ_of_accept 113 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 287 (accept_3_2 112 114 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 110 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 287 (accept_3_2 109 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 108 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 107 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 287 (accept_3_2 106 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  105 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 104 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 287 (accept_3_2 103 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 287 (accept_3_2 100 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 287 (Polychromatic418967fa.accept_16_3_2_15_1_7367 99 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 98 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 287 (accept_3_2 97 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 114 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 114 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 95 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 287 (accept_3_2 94 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 287 (accept_3_2 91 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 287 (Polychromatic418967fa.accept_21_6_9_14_1_8867 90 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 287 (accept_3_2 88 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 87 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 287 (accept_3_2 85 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 287 (accept_3_2 82 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 287
  (Polychromatic418967fa.accept_21_17_9_14_1_5700 80 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 114 287 (accept_3_2 79 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 114 287 (Polychromatic418967fa.accept_21_15_9_14_1_10462 78 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 287 (accept_3_2 76
  114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 114 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 287 (accept_3_2 73 114 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 114 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 114 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 71 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 114 287 (accept_3_2 70 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 114 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 287 (accept_3_2 67 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 287 (accept_3_2 64 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 114 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 114 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 287 (accept_3_2 61 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 287 (Polychromatic418967fa.accept_16_12_2_15_1_490 60 114
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 114 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 287 (accept_3_2 58 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 287 (accept_3_2 55 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 287 (accept_3_2 52 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 114 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 114 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 287 (accept_3_2 49 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 114 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 287 (accept_3_2 46 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 114 287 (Polychromatic418967fa.accept_16_12_2_15_1_490 44 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 287 (accept_3_2 43 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 114
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 287 (accept_3_2 40 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 287 (accept_3_2 37 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 287 (Polychromatic418967fa.accept_21_15_9_14_1_10462 36 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 287
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 287 (accept_3_2 34 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 287 (accept_3_2 31 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 287 (accept_3_2 28 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 287 (Polychromatic418967fa.accept_21_6_9_14_1_8867 27 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 287 (accept_3_2 25 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 114
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 287 (accept_3_2 22 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 287 (accept_3_2 19 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 287 (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 114 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 287 (accept_3_2 16 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 287 (accept_3_2 13 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 287 (accept_3_2 10 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 287 (accept_3_2 7 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 287 (Polychromatic418967fa.accept_21_6_9_14_1_8867 6 114 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 287 (accept_3_2 4 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 114 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 287 (accept_3_2 1 114 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 287 (allA_succ_of_accept 112 113 287 (accept_3_2 112 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 111 113 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 113
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 287 (accept_3_2 109 113
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 287
  (Polychromatic418967fa.accept_21_3_8_14_1_8864 108 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 113 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 107 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 287 (accept_3_2 106 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 113
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 104 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 287 (accept_3_2 103 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 287 (accept_3_2 100 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 99 113
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 287 (accept_3_2 97 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 95 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 287 (accept_3_2 94 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 287 (accept_3_2 91 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 89 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 287 (accept_3_2 88 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 287 (accept_3_2 85 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 287 (accept_3_2 82 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 81 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 287
  (Polychromatic418967fa.accept_13_2_9_1_1_67 80 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 287 (accept_3_2 79 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 287 (Polychromatic418967fa.accept_19_1_18_2_1_2835 77 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 287 (accept_3_2 76 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 287 (accept_3_2 73 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 287 (Polychromatic418967fa.accept_16_8_1_15_1_1982 72 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 287 (accept_3_2 70 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 68 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 287 (accept_3_2 67 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 287 (accept_3_2 64 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 287 (accept_3_2 61 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 59 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 287 (accept_3_2 58 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 287 (accept_3_2 55 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 287 (accept_3_2 52 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 287 (accept_3_2 49 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 287 (accept_3_2 46 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 287 (accept_3_2 43 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 287 (accept_3_2 40 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 287 (accept_3_2 37 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 287 (accept_3_2 34 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 287
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 287 (accept_3_2 31 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 287 (accept_3_2 28 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 287 (accept_3_2 25 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 287 (accept_3_2 22 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 287 (accept_3_2 19 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 287 (Polychromatic418967fa.accept_21_17_8_14_1_5638 17 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 287 (accept_3_2 16 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 287 (accept_3_2 13 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 287 (accept_3_2 10 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 287
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 287 (accept_3_2 7 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 287 (accept_3_2 4 113 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 287 (accept_3_2 1 113 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 287 (allA_of_3_0 112 112 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 287
  (allA_succ_of_accept 110 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 111 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 287 (accept_3_2 109 111 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 287 (Polychromatic418967fa.accept_17_6_9_15_1_3185 108 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 107 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 287 (accept_3_2 106 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 287 (accept_3_2 103 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 102
  111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 101 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 287 (accept_3_2 100 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 99 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 287 (accept_3_2 97 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 287 (accept_3_2 94 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 287 (accept_3_2 91 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 90 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 89 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 287 (accept_3_2 88 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 287 (accept_3_2 85 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 287 (accept_3_2 82 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 287 (accept_3_2 79 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 287 (accept_3_2 76 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 287 (Polychromatic418967fa.accept_17_7_9_15_1_8105 75 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 287 (accept_3_2 73 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 287 (accept_3_2 70 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 287 (accept_3_2 67 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 287 (accept_3_2 64 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 287 (accept_3_2 61 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 287 (accept_3_2 58 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 287 (accept_3_2 55 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 287 (accept_3_2 52 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 287 (accept_3_2 49 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 287 (accept_3_2 46 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 287 (accept_3_2 43 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 287 (accept_3_2 40 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 287 (Polychromatic418967fa.accept_21_18_6_14_1_2812 39 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 287 (accept_3_2 37 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 287
  (Polychromatic418967fa.accept_17_1_9_15_1_3186 35 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 287 (accept_3_2 34 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 287 (accept_3_2 31 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 287 (Polychromatic418967fa.accept_19_11_16_2_1_9759 30 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 287 (accept_3_2 28 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 287 (accept_3_2 25 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 287 (accept_3_2 22 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 287 (accept_3_2 19 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 287 (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 287
  (Polychromatic418967fa.accept_19_17_16_2_1_8390 17 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 287 (accept_3_2 16 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 287 (accept_3_2 13 111 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 287
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 111 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 287 (accept_3_2 10 111 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 287 (accept_3_2 7 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 287 (accept_3_2 4 111 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 111 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 287 (accept_3_2 1 111 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 287 (allA_succ_of_accept 109 110 287 (accept_3_2 109 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 108 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 107 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 110 287 (accept_3_2 106 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 287 (accept_3_2 103 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 110
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 287 (accept_3_2 100 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 98 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 287 (accept_3_2 97 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 110 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 287 (accept_3_2 94 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 92 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 287 (accept_3_2 91 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 90
  110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 287 (accept_3_2 88 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 287 (accept_3_2 85 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 83 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 287 (accept_3_2 82 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 287 (accept_3_2 79 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 110 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 287 (accept_3_2 76 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 74 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 287 (accept_3_2 73 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 110
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 287 (accept_3_2 70 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 287 (accept_3_2 67 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 287 (accept_3_2 64 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 287 (Polychromatic418967fa.accept_18_8_2_17_1_4782 62 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 287 (accept_3_2 61 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 110 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 287 (accept_3_2 58 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 287 (accept_3_2 55 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 110
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 287 (accept_3_2 52 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 287 (accept_3_2 49 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 287 (accept_3_2 46 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 287 (accept_3_2 43 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 287 (accept_3_2 40 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 287 (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 287 (accept_3_2 37 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 287 (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 110
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 287
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 287 (accept_3_2 34 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 287 (accept_3_2 31 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 287 (accept_3_2 28 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 287 (accept_3_2 25 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 287 (accept_3_2 22 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 287 (accept_3_2 19 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 110
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 287 (accept_3_2 16 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 287 (accept_3_2 13 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 287 (accept_3_2 10 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 287 (accept_3_2 7 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 287 (accept_3_2 4 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 287 (accept_3_2 1 110 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 287 (allA_of_3_0 109 109 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 287
  (allA_succ_of_accept 107 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 107 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 287 (accept_3_2 106 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 105 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 287
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 104 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 108 287 (accept_3_2 103 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 102 108 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 287
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 101 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 108 287 (accept_3_2 100 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 98 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 108 287 (accept_3_2 97 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 108 287
  (Polychromatic418967fa.accept_13_5_4_1_1_364 96 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 108 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 287 (accept_3_2 94 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 108 287 (Polychromatic418967fa.accept_16_13_12_15_1_6290 93 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 287
  (Polychromatic418967fa.accept_19_16_13_2_1_6920 92 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 108 287 (accept_3_2 91 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 108 287 (Polychromatic418967fa.accept_20_10_8_7_1_7834 90 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 89 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 287 (accept_3_2 88 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 287
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 287 (Polychromatic418967fa.accept_19_10_13_2_1_9771 86 108 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 287 (accept_3_2 85 108 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 108 287 (Polychromatic418967fa.accept_16_4_12_15_1_6289 84 108 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 108 287 (accept_3_2 82 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 108 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 81 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 108 287 (Polychromatic418967fa.accept_15_5_3_2_1_5930 80 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 287 (accept_3_2 79 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 108 287 (Polychromatic418967fa.accept_21_15_3_14_1_4141 78 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 287
  (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 108 287 (accept_3_2 76 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 74 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 287 (accept_3_2 73 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 287
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 287 (Polychromatic418967fa.accept_21_8_3_14_1_4165 71 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 287 (accept_3_2 70 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 69 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 287
  (Polychromatic418967fa.accept_13_3_4_1_1_363 68 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 287 (accept_3_2 67 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 66 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 287 (accept_3_2 64 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 287 (Polychromatic418967fa.accept_19_6_13_2_1_8365 63 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 287
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 62 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 287 (accept_3_2 61 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 287 (accept_3_2 58 108 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 57 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 287
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 108 287 (accept_3_2 55 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 108 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 287 (accept_3_2 52 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 287 (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 287 (accept_3_2 49 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 287 (Polychromatic418967fa.accept_17_14_6_15_1_3151 48 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 287
  (Polychromatic418967fa.accept_22_3_20_1_1_16200 47 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 108 287 (accept_3_2 46 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 108 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 287 (accept_3_2 43 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 287
  (Polychromatic418967fa.accept_13_3_4_1_1_363 42 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 287 (Polychromatic418967fa.accept_20_1_8_7_1_7856 41 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 287 (accept_3_2 40 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 287
  (Polychromatic418967fa.accept_21_17_3_14_1_2807 38 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 287 (accept_3_2 37 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 108 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 287 (accept_3_2 34 108 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 287
  (Polychromatic418967fa.accept_21_12_3_14_1_10498 33 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 108 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 287 (accept_3_2 31 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 287 (Polychromatic418967fa.accept_19_11_13_2_1_9770 30 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 287
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 287 (accept_3_2 28 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 287 (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 287 (accept_3_2 25 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 287
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 287 (accept_3_2 22 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 287 (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 287 (accept_3_2 19 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 287
  (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 287 (accept_3_2 16 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 287 (accept_3_2 13 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 287 (accept_3_2 10 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 287 (accept_3_2 7 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 287 (Polychromatic418967fa.accept_19_6_13_2_1_8365 6 108
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 287 (accept_3_2 4 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 287 (accept_3_2 1 108 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 287 (allA_succ_of_accept 106 107 287 (accept_3_2 106 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 287 (Polychromatic418967fa.accept_19_10_12_2_1_6948 105 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 287
  (Polychromatic418967fa.accept_19_9_12_2_1_9776 104 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 107 287 (accept_3_2 103 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 107 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 102 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 107 287
  (Polychromatic418967fa.accept_19_6_12_2_1_8379 101 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 107 287 (accept_3_2 100 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 107 287 (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 287 (Polychromatic418967fa.accept_13_7_3_1_1_814
  98 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 287 (accept_3_2 97
  107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 96 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 95 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 287 (accept_3_2 94 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 93 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 287 (accept_3_2 91 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 287 (Polychromatic418967fa.accept_16_10_11_15_1_6302 90 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 89 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 287 (accept_3_2 88 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 287
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 87 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 107 287 (Polychromatic418967fa.accept_14_2_9_7_1_5633 86 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 287 (accept_3_2 85 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 83 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 287 (accept_3_2 82 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 287 (accept_3_2 79 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 287 (Polychromatic418967fa.accept_17_10_5_15_1_4332 78 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 287
  (Polychromatic418967fa.accept_19_1_12_2_1_6918 77 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 287 (accept_3_2 76 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 75 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 287 (Polychromatic418967fa.accept_16_10_11_15_1_6302 74 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 287 (accept_3_2 73 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 287 (accept_3_2 70 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 69 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 287 (accept_3_2 67 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 287 (Polychromatic418967fa.accept_19_9_12_2_1_9776 66 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 65 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 287 (accept_3_2 64 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 287 (Polychromatic418967fa.accept_17_11_5_15_1_8144 62 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 287 (accept_3_2 61 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 287 (accept_3_2 58 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 287 (accept_3_2 55 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 287
  (Polychromatic418967fa.accept_21_11_2_14_1_7225 53 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 107 287 (accept_3_2 52 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 107 287 (Polychromatic418967fa.accept_16_3_11_15_1_1963 51 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 287 (accept_3_2 49 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 47 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 287 (accept_3_2 46 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 287 (accept_3_2 43 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 287 (Polychromatic418967fa.accept_16_10_11_15_1_6302 42 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 287 (accept_3_2 40 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 287
  (Polychromatic418967fa.accept_21_17_2_14_1_7208 38 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 107 287 (accept_3_2 37 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 107 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 287 (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 287 (accept_3_2 34 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 107 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 287 (accept_3_2 31 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 107 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 287
  (Polychromatic418967fa.accept_19_10_12_2_1_6948 29 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 107 287 (accept_3_2 28 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 107 287 (Polychromatic418967fa.accept_17_10_5_15_1_4332 27 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  26 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 287 (accept_3_2 25
  107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 107 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 287 (accept_3_2 22 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 287 (Polychromatic418967fa.accept_27_21_26_17_1_17624 21 107 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 287 (accept_3_2 19 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 287 (accept_3_2 16 107 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 287
  (Polychromatic418967fa.accept_19_14_12_2_1_6878 14 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 107 287 (accept_3_2 13 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 107 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 287 (accept_3_2 10 107
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 287
  (Polychromatic418967fa.accept_19_9_12_2_1_9776 9 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 287 (Polychromatic418967fa.accept_21_8_2_14_1_10496 8 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 287 (accept_3_2 7 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 107 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398
  5 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 287 (accept_3_2 4
  107 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 287
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 107 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 107 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 287 (accept_3_2 1 107 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 107
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 287 (allA_of_3_0 106 106 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 287
  (allA_succ_of_accept 104 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 287 (accept_3_2 103 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 287 (accept_3_2 100 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 105 287 7 14 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 105 287 (accept_3_2 97 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 105 287 (Polychromatic418967fa.accept_18_6_15_17_1_7363 96 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 287 (Polychromatic418967fa.accept_9_5_6_8_1_101
  95 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 287 (accept_3_2 94
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 93 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 105 287 7 13 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 287
  (Polychromatic418967fa.accept_19_13_10_2_1_12473 89 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 105 287 (accept_3_2 88 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 105 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 287 (accept_3_2 85 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 287 7 12 15 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 287 (accept_3_2 82 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 81 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 287 (accept_3_2 79 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 287 7 11 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 287 (accept_3_2 76 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 105 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  75 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 287 (accept_3_2 73 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 105 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 287 7 10 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 287
  (Polychromatic418967fa.accept_17_1_3_15_1_2153 69 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 287 (accept_3_2 67 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 287 (Polychromatic418967fa.accept_9_2_6_8_1_321
  65 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 287 (accept_3_2 64
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 287 7 9 15 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 287 (accept_3_2 61 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 105 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 287 (accept_3_2 58 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 105 287 7 8 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 287 (accept_3_2 55 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 287 (accept_3_2 52 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 105 287 7 7 15 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 105 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 287 (accept_3_2 46 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 287 (accept_3_2 43 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  105 287 7 6 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 105 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 105 287 (accept_3_2 40 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 287 (accept_3_2 37 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 287
  (Polychromatic418967fa.accept_19_17_10_2_1_9793 36 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 105 287 7 5 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 105 287 (accept_3_2 34 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 287 (accept_3_2 31 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 105 287 7 4 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 105 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 287 (accept_3_2 25 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 287
  (Polychromatic418967fa.accept_16_8_9_15_1_5112 24 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 287 (accept_3_2 22 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 105 287 7 3 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 287 (accept_3_2 19 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 287
  (Polychromatic418967fa.accept_19_17_10_2_1_9793 17 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 287 (accept_3_2 16 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 105 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 105 287 7 2 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 287 (accept_3_2 13 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 287 (accept_3_2 10 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 287 7 1 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 287 (accept_3_2 4 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 287 (accept_3_2 1 105 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 287 (allA_succ_of_accept 103 104 287 (accept_3_2 103 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 287 (accept_3_2 100 104
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 287 (accept_3_2 97 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 95 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 287 (accept_3_2 94 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 287 (accept_3_2 91 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 287 (Polychromatic418967fa.accept_21_6_20_14_1_8837 90 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 287
  (Polychromatic418967fa.accept_16_9_8_15_1_5095 89 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 287 (accept_3_2 88 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 287 (accept_3_2 85 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 287 (accept_3_2 82 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 287 (accept_3_2 79 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 287
  (Polychromatic418967fa.accept_19_1_9_2_1_6945 77 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 287 (accept_3_2 76 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 287 (accept_3_2 73 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 71 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 287 (accept_3_2 70 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 287 (Polychromatic418967fa.accept_16_4_8_15_1_1113 68 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 287 (accept_3_2 67 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 287 (accept_3_2 64 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 287 (accept_3_2 61 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 287
  (Polychromatic418967fa.accept_21_17_20_14_1_11808 59 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 104 287 (accept_3_2 58 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 287 (accept_3_2 55 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 287
  (Polychromatic418967fa.accept_23_8_12_11_1_11312 54 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 287 (accept_3_2 52 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 50 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 287 (accept_3_2 49 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 287 (accept_3_2 46 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 287
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 104 287 (accept_3_2 43 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 104
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 287 (accept_3_2 40 104
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 287 (accept_3_2 37 104 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 104 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 287 (accept_3_2 34 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 287 (accept_3_2 31 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 287 (accept_3_2 28 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 287 (accept_3_2 25 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 287 (accept_3_2 22 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 287 (accept_3_2 19 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 287 (accept_3_2 16 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 287 (accept_3_2 13 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 287 (accept_3_2 10 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 287 (accept_3_2 7 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 287 (accept_3_2 4 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 287 (accept_3_2 1 104 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 287 (allA_of_3_0 103 103 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 287 (allA_succ_of_accept 101
  102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 287 (accept_3_2 100 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 99 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 98 102
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 287 (accept_3_2 97 102
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 96 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 287 (accept_3_2 94 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 287 (Polychromatic418967fa.accept_9_2_3_8_1_318
  92 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 287 (accept_3_2 91
  102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 90 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 287 (accept_3_2 88 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 287 (Polychromatic418967fa.accept_9_5_3_8_1_316
  86 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 287 (accept_3_2 85
  102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 84 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 287 (accept_3_2 82 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 287
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 80 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 287 (accept_3_2 79 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 287 (accept_3_2 76 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 287 (accept_3_2 73 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 287 (Polychromatic418967fa.accept_16_7_6_15_1_495 71 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 287 (accept_3_2 70 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 287 (accept_3_2 67 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 287 (accept_3_2 64 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 102 287 (accept_3_2 61 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 287 (accept_3_2 58 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 287 (accept_3_2 55 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 287 (accept_3_2 52 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 287 (accept_3_2 49 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 287 (accept_3_2 46 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 287 (accept_3_2 43 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 287 (accept_3_2 40 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 287 (accept_3_2 37 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 287 (accept_3_2 34 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 287 (accept_3_2 31 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 287 (Polychromatic418967fa.accept_21_9_18_14_1_5648 30 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 287 (accept_3_2 28 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 287 (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 287
  (Polychromatic418967fa.accept_21_5_18_14_1_2793 26 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 102 287 (accept_3_2 25 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 287 (accept_3_2 22 102 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 287 (accept_3_2 19 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 287 (accept_3_2 16 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 287 (accept_3_2 13 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 287 (accept_3_2 10 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 287 (accept_3_2 7 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 287 (accept_3_2 4 102 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 102 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 287 (accept_3_2 1 102 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 287 (allA_succ_of_accept 100 101 287 (accept_3_2 100 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 99 101 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 287 (accept_3_2 97 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  96 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 287 (accept_3_2 94 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 287 (Polychromatic418967fa.accept_18_2_11_17_1_4773 92 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 287 (accept_3_2 91 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 287
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 89 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 101 287 (accept_3_2 88 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 101 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 287 (accept_3_2 85 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  84 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 287
  (Polychromatic418967fa.accept_21_20_17_14_1_10489 83 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 101 287 (accept_3_2 82 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 101 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 81 101 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 101
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 287 (accept_3_2 79 101
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 101 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 287 (accept_3_2 76 101 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 287 (accept_3_2 73
  101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 287
  (Polychromatic418967fa.accept_17_4_16_15_1_1212 72 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 287 (Polychromatic418967fa.accept_20_11_1_7_1_9233 71 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 287 (accept_3_2 70 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 287 (accept_3_2 67 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 287 (accept_3_2 64 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 101
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 287 (accept_3_2 61 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 287 (accept_3_2 58 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 287
  (Polychromatic418967fa.accept_10_6_1_7_1_342 56 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 287 (accept_3_2 55 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 287 (accept_3_2 52 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 287 (accept_3_2 49 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 287 (accept_3_2 46 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 287 (Polychromatic418967fa.accept_17_11_16_15_1_5467 45
  101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 287
  (Polychromatic418967fa.accept_10_4_1_7_1_371 44 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 287 (accept_3_2 43 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 287 (accept_3_2 40 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 287 (accept_3_2 37 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 287 (accept_3_2 34 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 287 (accept_3_2 31 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 287 (Polychromatic418967fa.accept_19_10_6_2_1_6907 29 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 287 (accept_3_2 28 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 287 (Polychromatic418967fa.accept_19_8_6_2_1_11146 27 101
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 287 (accept_3_2 25 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 287 (accept_3_2 22 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 287 (accept_3_2 19 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 287 (accept_3_2 16 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 287 (accept_3_2 13 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 287 (accept_3_2 10 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 101
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 287
  (Polychromatic418967fa.accept_19_8_6_2_1_11146 8 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 287 (accept_3_2 7 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 287 (accept_3_2 4 101 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 287 (accept_3_2 1 101 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 287 (allA_of_3_0 100 100 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 287 (allA_succ_of_accept 98 99
  287 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 287 (accept_3_2 97 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 96 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 287 (Polychromatic418967fa.accept_22_7_11_1_1_6711 95 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 287 (accept_3_2 94 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 99
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 287 (accept_3_2 91 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 90 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 89 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 287 (accept_3_2 88 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 87 99 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 287 (accept_3_2 85 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 83 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 287 (accept_3_2 82 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 287 (accept_3_2 79 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 77 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 287 (accept_3_2 76 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 287 (accept_3_2 73 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 71 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 287 (accept_3_2 70 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 287 (accept_3_2 67 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 287 (Polychromatic418967fa.accept_16_2_3_15_1_6309 66 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 287 (Polychromatic418967fa.accept_22_21_11_1_1_13201 65 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 287 (accept_3_2 64 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 99
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 287 (accept_3_2 61 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 287 (accept_3_2 58 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 287 (accept_3_2 55 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 287 (Polychromatic418967fa.accept_17_3_14_15_1_5502 54 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 287 (accept_3_2 52 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 287 (accept_3_2 49 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 287 (Polychromatic418967fa.accept_19_9_4_2_1_9753 47 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 287 (accept_3_2 46 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 287 (accept_3_2 43 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 287 (accept_3_2 40 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 99
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 287 (accept_3_2 37 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 287 (accept_3_2 34 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 287 (accept_3_2 31 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 287 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 287 (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 287 (accept_3_2 28 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 99
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 287 (accept_3_2 25 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 287 (accept_3_2 22 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 287 (accept_3_2 19 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 287 (Polychromatic418967fa.accept_19_17_4_2_1_8360 17 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 287 (accept_3_2 16 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 287 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 99
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 287 (accept_3_2 13 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 287 (accept_3_2 10 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 287 (accept_3_2 7 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 99 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 287 (accept_3_2 4 99 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 287 (Polychromatic418967fa.accept_17_3_14_15_1_5502 3 99 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 287 (accept_3_2 1 99 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  287 (allA_succ_of_accept 97 98 287 (accept_3_2 97 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 96 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 287 (accept_3_2 94 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 98 287 7 13 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 98 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 287 (accept_3_2 88 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 86 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 287 (accept_3_2 85 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98
  287 7 12 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  98 287 (Polychromatic418967fa.accept_16_3_2_15_1_7367 83 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 98 287 (accept_3_2 82 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 98 287 (accept_3_2 79 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 98 287
  (Polychromatic418967fa.accept_25_3_23_12_1_5201 78 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 98 287 7 11 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 98 287 (accept_3_2 76 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 98 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 74 98 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 98 287 (accept_3_2 73 98 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 98 287 (Polychromatic418967fa.accept_23_3_6_11_1_17622 72 98
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 98 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 98 287 7 10 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 98
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 98 287 (accept_3_2 67 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 98 287 (Polychromatic418967fa.accept_15_6_8_2_1_104
  66 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 98 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 98 287 (accept_3_2 64 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 98
  287 7 9 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  98 287 (Polychromatic418967fa.accept_17_11_13_15_1_2140 62 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 98 287 (accept_3_2 61 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 98 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 98 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 287 (accept_3_2 58 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 287 7 8 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 287 (accept_3_2 55
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 98 287
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 287 (accept_3_2 52 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386
  50 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 98 287 7 7 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 98 287
  (Polychromatic418967fa.accept_28_20_14_7_1_17623 48 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 287 (accept_3_2 46 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 287 (accept_3_2 43 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  287 7 6 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 98 287 (accept_3_2 40 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 98
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 287 (accept_3_2 37 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 287 (Polychromatic418967fa.accept_15_6_8_2_1_104
  36 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 98 287 7 5 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 98 287 (accept_3_2 34
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 98 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 287 (accept_3_2 31 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 98 287 (Polychromatic418967fa.accept_19_11_3_2_1_12485 30 98 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 287 7 4 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 287 (Polychromatic418967fa.accept_23_3_6_11_1_17622 26 98
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 287 (accept_3_2 25 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  24 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 98 287 (accept_3_2 22 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98
  287 7 3 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  98 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 98 287 (accept_3_2 19 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 98 287 (Polychromatic418967fa.accept_19_18_3_2_1_6939 18 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 287 (accept_3_2 16 98 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 287 7 2 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 287 (accept_3_2 13
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 287
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 98 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 287 (accept_3_2 10 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 98 287 7 1 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 98 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 6 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 287 (accept_3_2 4 98 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 98 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 287 (accept_3_2 1 98
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  287 (allA_of_3_0 97 97 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 287 (allA_succ_of_accept 95 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 287 (accept_3_2 94 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 287 (accept_3_2 91 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 90 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 287
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 89 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 287 (accept_3_2 88 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 287 (accept_3_2 85 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 287 (accept_3_2 82 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 287 (Polychromatic418967fa.accept_22_14_8_1_1_14681 80 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 287 (accept_3_2 79 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 287 (Polychromatic418967fa.accept_21_15_12_14_1_7232 78 96
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 287 (accept_3_2 76 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 287 (accept_3_2 73 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 72 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 287 (accept_3_2 70 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 69 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 287 (accept_3_2 67 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 287 (accept_3_2 64 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 287 (Polychromatic418967fa.accept_22_18_8_1_1_11637 62 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 287 (accept_3_2 61 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 60 96 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 287 (accept_3_2 58 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 287 (accept_3_2 55 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 287 (Polychromatic418967fa.accept_26_2_18_1_1_15901 54 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 287 (accept_3_2 52 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 287 (accept_3_2 49 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 287 (accept_3_2 46 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 287 (accept_3_2 43 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 287 (accept_3_2 40 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 287 (accept_3_2 37 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 287 (Polychromatic418967fa.accept_21_15_12_14_1_7232 36 96 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 287
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 287 (accept_3_2 34 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 287 (accept_3_2 31 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 287 (accept_3_2 28 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 287 (accept_3_2 25 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 24 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 287 (accept_3_2 22 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 287 (accept_3_2 19 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 287 (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 287
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 287 (accept_3_2 16 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 287 (accept_3_2 13 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 287 (accept_3_2 10 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 287 (accept_3_2 7 96 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 96 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 287 (accept_3_2 4 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 96 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 287 (accept_3_2 1 96 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 287
  (allA_succ_of_accept 94 95 287 (accept_3_2 94 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 287 (accept_3_2 91 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 90 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 89 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 287 (accept_3_2 88 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 86 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 287 (accept_3_2 85 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 287 (accept_3_2 82 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 81 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 80 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 287 (accept_3_2 79 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 287
  (Polychromatic418967fa.accept_22_11_7_1_1_13135 77 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 287 (accept_3_2 76 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 287 (accept_3_2 73 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 287 (accept_3_2 70 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 287 (accept_3_2 67 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 287 (accept_3_2 64 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 287 (accept_3_2 61 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 287 (accept_3_2 58 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 287 (accept_3_2 55 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 287 (Polychromatic418967fa.accept_21_12_11_14_1_7239 54 95 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 287 (accept_3_2 52 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 287 (accept_3_2 49 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 287 (accept_3_2 46 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 287 (accept_3_2 43 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 287 (accept_3_2 40 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 287 (accept_3_2 37 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 287
  (Polychromatic418967fa.accept_23_12_3_11_1_17621 35 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 95 287 (accept_3_2 34 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 95 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 95 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 287 (accept_3_2 31 95 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30
  95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 287 (accept_3_2 28 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 287 (accept_3_2 25 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 287 (accept_3_2 22 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 287 (accept_3_2 19 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 287 (accept_3_2 16 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 287 (accept_3_2 13 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 287 (accept_3_2 10 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 287 (Polychromatic418967fa.accept_25_9_20_12_1_17620 9 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 287 (accept_3_2 7 95 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 287
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 287 (accept_3_2 4 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 287 (accept_3_2 1 95 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 287
  (allA_of_3_0 94 94 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 287 (allA_succ_of_accept 92 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 287 (accept_3_2 91 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 89 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 287 (accept_3_2 88 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 287 (accept_3_2 85 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 287 (accept_3_2 82 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 287 (accept_3_2 79 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 287 (accept_3_2 76 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 287 (accept_3_2 73 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 287 (accept_3_2 70 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 287 (accept_3_2 67 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 287 (accept_3_2 64 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 287 (accept_3_2 61 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 287 (accept_3_2 58 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 287 (accept_3_2 55 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 287 (Polychromatic418967fa.accept_19_15_17_2_1_4097 53 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 287 (accept_3_2 52 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 287 (accept_3_2 49 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 287 (accept_3_2 46 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 287 (accept_3_2 43 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 287 (accept_3_2 40 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 287 (accept_3_2 37 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 287 (accept_3_2 34 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 287 (accept_3_2 31 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 287 (accept_3_2 28 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 287 (accept_3_2 25 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 287 (accept_3_2 22 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 287 (Polychromatic418967fa.accept_22_21_5_1_1_6731 21 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 287 (accept_3_2 19 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 287 (accept_3_2 16 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 287 (accept_3_2 13 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 287 (accept_3_2 10 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 287 (accept_3_2 7 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 287 (accept_3_2 4 93 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 287 (accept_3_2 1 93 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 287
  (allA_succ_of_accept 91 92 287 (accept_3_2 91 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 90 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 89 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 287 (accept_3_2 88 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 287 (accept_3_2 85 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 287 (accept_3_2 82 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 80 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 287 (accept_3_2 79 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 287 (accept_3_2 76 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 74 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 287 (accept_3_2 73 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 287 (Polychromatic418967fa.accept_14_1_8_7_1_1253 71 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 287 (accept_3_2 70 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 287 (accept_3_2 67 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 65 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 287 (accept_3_2 64 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 287 (accept_3_2 61 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 287 (accept_3_2 58 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 287
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 287 (accept_3_2 55 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 53 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 287 (accept_3_2 52 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 287 (accept_3_2 49 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 287 (accept_3_2 46 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 287 (accept_3_2 43 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 287 (accept_3_2 40 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 287 (accept_3_2 37 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 287 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 287 (accept_3_2 34 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 287 (accept_3_2 31 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 287 (accept_3_2 28 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 287 (accept_3_2 25 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 287 (accept_3_2 22 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 287
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 287 (accept_3_2 19 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 287 (Polychromatic418967fa.accept_19_17_16_2_1_8390 17 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 287 (accept_3_2 16 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 287 (accept_3_2 13 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 287 (accept_3_2 10 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 287 (accept_3_2 7 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 287 (accept_3_2 4 92 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  92 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 287 (accept_3_2 1 92 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 287
  (allA_of_3_0 91 91 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 287 (allA_succ_of_accept 89 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 287 (accept_3_2 88 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 86 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 287 (accept_3_2 85 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 287 (Polychromatic418967fa.accept_19_8_14_2_1_9774 84 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 287
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 83 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 287 (accept_3_2 82 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 90 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 287 (accept_3_2 79 90 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 78 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 287 (accept_3_2 76 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 287 (Polychromatic418967fa.accept_16_11_10_15_1_6301 75 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 287 (Polychromatic418967fa.accept_19_17_14_2_1_4116 74 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 287 (accept_3_2 73 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 287 (Polychromatic418967fa.accept_21_9_6_14_1_7228 72 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 287
  (Polychromatic418967fa.accept_14_1_6_7_1_1936 71 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 287 (accept_3_2 70 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 287 (Polychromatic418967fa.accept_20_8_10_7_1_6291 68 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 287 (accept_3_2 67 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 287 (Polychromatic418967fa.accept_21_3_6_14_1_5717 66 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 287 (accept_3_2 64 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 62 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 287 (accept_3_2 61 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 287
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 59 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 287 (accept_3_2 58 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 287 (Polychromatic418967fa.accept_22_12_2_1_1_14678 56 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 287 (accept_3_2 55 90 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  54 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 287 (accept_3_2 52 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 287 (Polychromatic418967fa.accept_20_11_10_7_1_9280 51 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 50 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 287 (accept_3_2 49 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 287 (Polychromatic418967fa.accept_20_8_10_7_1_6291 48 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 287 (accept_3_2 46 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 287 (accept_3_2 43 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 287 (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 287 (accept_3_2 40 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 287 (Polychromatic418967fa.accept_19_1_14_2_1_4134 39 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 287 (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 287 (accept_3_2 37 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 90 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 287
  (Polychromatic418967fa.accept_19_16_14_2_1_6924 35 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 287 (accept_3_2 34 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 287 (accept_3_2 31 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 30 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 287 (accept_3_2 28 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 287 (Polychromatic418967fa.accept_19_7_14_2_1_4095 26 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 287 (accept_3_2 25 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 287
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 23 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 287 (accept_3_2 22 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 287 (Polychromatic418967fa.accept_19_1_14_2_1_4134 20 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 287 (accept_3_2 19 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 287 (accept_3_2 16 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 90 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 287 (accept_3_2 13 90 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 287 (Polychromatic418967fa.accept_19_12_14_2_1_1692 12 90 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 287 (accept_3_2 10 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 90 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 287 (accept_3_2 7 90 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 287 (Polychromatic418967fa.accept_22_6_2_1_1_6763 6 90 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 287 (accept_3_2 4 90 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 287
  (Polychromatic418967fa.accept_13_2_12_1_1_343 2 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 287 (accept_3_2 1 90 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 287
  (allA_succ_of_accept 88 89 287 (accept_3_2 88 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 87 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 287 (accept_3_2 85 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 287 (Polychromatic418967fa.accept_17_16_4_15_1_4342 84 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 287
  (Polychromatic418967fa.accept_19_7_13_2_1_2878 83 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 287 (accept_3_2 82 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 287 (accept_3_2 79 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 287
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 287 (accept_3_2 76 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 75 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 287 (accept_3_2 73 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 287
  (Polychromatic418967fa.accept_21_8_5_14_1_5660 71 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 287 (accept_3_2 70 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 287 (Polychromatic418967fa.accept_25_19_14_12_1_17619 69 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 68 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 287 (accept_3_2 67 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 287
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 65 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 287 (accept_3_2 64 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 287 (accept_3_2 61 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 287
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 59 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 287 (accept_3_2 58 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 57 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 287 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 287 (accept_3_2 55 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 287
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 287 (accept_3_2 52 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 287 (accept_3_2 49 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 287 (accept_3_2 46 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 287 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 287 (accept_3_2 43 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 287
  (Polychromatic418967fa.accept_21_20_5_14_1_5661 41 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 287 (accept_3_2 40 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 287 (Polychromatic418967fa.accept_19_1_13_2_1_6923 39 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 287 (accept_3_2 37 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 287
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 287 (accept_3_2 34 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 287 (accept_3_2 31 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 287 (accept_3_2 28 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 287 (accept_3_2 25 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 287 (Polychromatic418967fa.accept_16_8_9_15_1_5112 24 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 287 (accept_3_2 22 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 287 (accept_3_2 19 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 287
  (Polychromatic418967fa.accept_20_17_9_7_1_13576 17 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 287 (accept_3_2 16 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 287 (Polychromatic418967fa.accept_19_15_13_2_1_6851 15 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 287 (accept_3_2 13 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 287
  (Polychromatic418967fa.accept_17_11_4_15_1_3150 11 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 287 (accept_3_2 10 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 287 (accept_3_2 7 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 287 (accept_3_2 4 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 89 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 287 (accept_3_2 1 89 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 287
  (allA_of_3_0 88 88 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 287 (allA_succ_of_accept 86 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 287 (accept_3_2 85 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 287 (accept_3_2 82 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 287 (accept_3_2 79 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 78 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 287 (accept_3_2 76 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 287 (accept_3_2 73 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 287 (Polychromatic418967fa.accept_16_8_7_15_1_6339 72 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 287 (accept_3_2 70 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 287 (accept_3_2 67 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 287 (accept_3_2 64 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 287 (accept_3_2 61 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 287 (accept_3_2 58 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 287 (accept_3_2 55 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 287 (accept_3_2 52 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 287 (accept_3_2 49 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 287 (accept_3_2 46 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 287 (accept_3_2 43 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 287 (accept_3_2 40 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 287 (accept_3_2 37 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 287 (accept_3_2 34 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 287 (accept_3_2 31 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 287 (accept_3_2 28 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 287 (accept_3_2 25 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 287 (accept_3_2 22 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 287 (accept_3_2 19 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 287 (Polychromatic418967fa.accept_21_17_3_14_1_2807 17 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 287 (accept_3_2 16 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 87 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 287 (accept_3_2 13 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 287 (accept_3_2 10 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 287 (accept_3_2 7 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 87 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 287 (accept_3_2 4 87 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 287 (accept_3_2 1 87 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 287
  (allA_succ_of_accept 85 86 287 (accept_3_2 85 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 287 (accept_3_2 82 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 287 (accept_3_2 79 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 287 (accept_3_2 76 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 287 (accept_3_2 73 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 287 (accept_3_2 70 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 287 (accept_3_2 67 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 287 (accept_3_2 64 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 287
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 62 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 287 (accept_3_2 61 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 287 (accept_3_2 58 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 287 (accept_3_2 55 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 287 (accept_3_2 52 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 287
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 50 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 287 (accept_3_2 49 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 287 (accept_3_2 46 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 287 (accept_3_2 43 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 287 (accept_3_2 40 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 287 (accept_3_2 37 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 287 (accept_3_2 34 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 287
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 287 (accept_3_2 31 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 287 (accept_3_2 28 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 287
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 287 (accept_3_2 25 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 287 (accept_3_2 22 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 287 (accept_3_2 19 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 287 (accept_3_2 16 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 287
  (Polychromatic418967fa.accept_22_14_20_1_1_6722 14 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 287 (accept_3_2 13 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 287 (accept_3_2 10 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 287 (accept_3_2 7 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 287 (accept_3_2 4 86 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 287 (accept_3_2 1 86 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 287
  (allA_of_3_0 85 85 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 287 (allA_succ_of_accept 83 84 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 287 (accept_3_2 82 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 80 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 287 (accept_3_2 79 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 84 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 84 287 7 11 12 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 84 287 (accept_3_2 76 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75
  84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 84 287 (accept_3_2 73 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  84 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 84 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 287 7 10 12 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 287 (accept_3_2 67 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 84 287 (Polychromatic418967fa.accept_24_18_12_23_1_12692 66 84 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 287 (accept_3_2 64 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84
  287 7 9 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  84 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 84 287 (accept_3_2 61 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 287 (accept_3_2 58 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 287 (Polychromatic418967fa.accept_13_5_6_1_1_822
  57 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 287 7 8 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 287 (accept_3_2 55
  84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 287
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 287 (accept_3_2 52 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50
  84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84 287 7 7 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 84 287
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 287 (accept_3_2 46 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 287 (Polychromatic418967fa.accept_17_11_16_15_1_5467 45 84 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 44 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 287 (accept_3_2 43 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84
  287 7 6 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 84 287 (accept_3_2 40 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 84 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 287 (accept_3_2 37 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 287
  (Polychromatic418967fa.accept_22_14_18_1_1_13125 36 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 84 287 7 5 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 84 287 (accept_3_2 34 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 287 (accept_3_2 31 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 287
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 287 7 4 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 287
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 287 (accept_3_2 25 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 287 (accept_3_2 22 84 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 287 7 3 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 84 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 287 (accept_3_2 19 84 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 287 (accept_3_2 16 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 287 7 2 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 287 (accept_3_2 13 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 84 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 287 (accept_3_2 10 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9
  84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 84 287 7 1 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 84 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 287 (accept_3_2 4 84 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 287 (accept_3_2 1 84 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 287
  (allA_succ_of_accept 82 83 287 (accept_3_2 82 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 81 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 287 (Polychromatic418967fa.accept_19_4_7_2_1_6944 80 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 287 (accept_3_2 79 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 287 (accept_3_2 76 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 74 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 287 (accept_3_2 73 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 287 (Polychromatic418967fa.accept_21_9_20_14_1_4139 72 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 287 (accept_3_2 70 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 287 (accept_3_2 67 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 287 (accept_3_2 64 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 287 (Polychromatic418967fa.accept_24_15_11_23_1_14295 63 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 287 (accept_3_2 61 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 287 (accept_3_2 58 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 287 (accept_3_2 55 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 287
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 53 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 83 287 (accept_3_2 52 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 83 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 287 (accept_3_2 49 83 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48
  83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 287 (accept_3_2 46 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 287 (accept_3_2 43 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 287 (accept_3_2 40 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 287 (accept_3_2 37 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 287 (accept_3_2 34 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 287 (accept_3_2 31 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 287 (accept_3_2 28 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 287 (accept_3_2 25 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 287 (accept_3_2 22 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 287 (accept_3_2 19 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 287
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 287 (accept_3_2 16 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 287 (accept_3_2 13 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 287
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 287 (accept_3_2 10 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 287 (accept_3_2 7 83 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 287 (accept_3_2 4 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 287 (Polychromatic418967fa.accept_16_2_3_15_1_6309 2 83 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 287 (accept_3_2 1 83 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 287 (allA_of_3_0 82 82 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 287
  (allA_succ_of_accept 80 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 287 (accept_3_2 79 81 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 287
  (Polychromatic418967fa.accept_22_11_15_1_1_8397 77 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 287 (accept_3_2 76 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  81 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 287 (accept_3_2 73 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 287 (accept_3_2 70 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 69 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 287 (accept_3_2 67 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 287
  (Polychromatic418967fa.accept_19_8_5_2_1_4105 65 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 287 (accept_3_2 64 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 287 (accept_3_2 61 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 287 (Polychromatic418967fa.accept_14_4_11_7_1_1234 60 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 59 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 287 (accept_3_2 58 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 287 (accept_3_2 55 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 287 (accept_3_2 52 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 287 (accept_3_2 49 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 287 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 287
  (Polychromatic418967fa.accept_21_5_18_14_1_2793 47 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 287 (accept_3_2 46 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 287 (accept_3_2 43 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 287 (accept_3_2 40 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 287 (accept_3_2 37 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 287
  (Polychromatic418967fa.accept_19_16_5_2_1_8375 35 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 287 (accept_3_2 34 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 287 (accept_3_2 31 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 287
  (Polychromatic418967fa.accept_19_10_5_2_1_9784 29 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 287 (accept_3_2 28 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 287 (accept_3_2 25 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 287 (accept_3_2 22 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 21 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 287 (accept_3_2 19 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 287
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 287 (accept_3_2 16 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 287 (accept_3_2 13 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 287 (accept_3_2 10 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 287 (Polychromatic418967fa.accept_21_9_18_14_1_5648 9 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 287 (accept_3_2 7 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 287 (accept_3_2 4 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 287 (accept_3_2 1 81 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 287 (allA_succ_of_accept 79 80 287 (accept_3_2 79 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 78 80 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 77 80
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 287 (accept_3_2 76 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 287 (accept_3_2 73 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 287 (accept_3_2 70 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 68 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 287 (accept_3_2 67 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 287 (Polychromatic418967fa.accept_19_9_4_2_1_9753 66 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 287 (Polychromatic418967fa.accept_17_14_12_15_1_5558 65 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 287 (accept_3_2 64 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 287 (accept_3_2 61 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 59 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 287 (accept_3_2 58 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 56 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 287 (accept_3_2 55 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 287 (Polychromatic418967fa.accept_17_3_12_15_1_1203 54 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 287 (accept_3_2 52 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 287 (accept_3_2 49 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 287 (Polychromatic418967fa.accept_19_9_4_2_1_9753 47 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 287 (accept_3_2 46 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 287 (accept_3_2 43 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 287 (accept_3_2 40 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 287 (accept_3_2 37 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 287 (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 287 (accept_3_2 34 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 287
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 287 (accept_3_2 31 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 287 (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 287 (accept_3_2 28 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 287 (accept_3_2 25 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 287 (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 287 (accept_3_2 22 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 287
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 20 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 287 (accept_3_2 19 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 287 (accept_3_2 16 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 287 (accept_3_2 13 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 287 (accept_3_2 10 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 287
  (Polychromatic418967fa.accept_21_8_17_14_1_4156 8 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 287 (accept_3_2 7 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 80 287 (Polychromatic418967fa.accept_18_5_8_17_1_3478 5 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 287 (accept_3_2 4 80 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 287 (accept_3_2 1 80 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 287 (allA_of_3_0 79
  79 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 287 (allA_succ_of_accept 77 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 287 (accept_3_2 76 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 287 (accept_3_2 73 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 287
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 71 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 287 (accept_3_2 70 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 287 (accept_3_2 67 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 287 (accept_3_2 64 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 287 (Polychromatic418967fa.accept_22_19_12_1_1_11606 63 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 62 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 287 (accept_3_2 61 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 287 (Polychromatic418967fa.accept_21_18_15_14_1_8871 60 78 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 287 (accept_3_2 58 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 287 (accept_3_2 55 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 287 (Polychromatic418967fa.accept_21_12_15_14_1_8851 54 78 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 287 (accept_3_2 52 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 51 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 287 (accept_3_2 49 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 287 (accept_3_2 46 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 287 (accept_3_2 43 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 78
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 287 (accept_3_2 40 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 287 (accept_3_2 37 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 287 (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 287 (accept_3_2 34 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 287 (accept_3_2 31 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 287 (accept_3_2 28 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 287 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 287 (accept_3_2 25 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 287 (Polychromatic418967fa.accept_21_3_15_14_1_5722 24 78
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 287 (accept_3_2 22 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 287 (accept_3_2 19 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 287 (Polychromatic418967fa.accept_21_18_15_14_1_8871 18 78 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 287 (accept_3_2 16 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 287 (accept_3_2 13 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 78 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 287 (accept_3_2 10 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 287 (Polychromatic418967fa.accept_17_8_10_15_1_9328 8 78 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 287 (accept_3_2 7 78 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 78 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 287 (accept_3_2 4 78 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 287 (accept_3_2 1 78 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 287
  (allA_succ_of_accept 76 77 287 (accept_3_2 76 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 287 (accept_3_2 73 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 287 (Polychromatic418967fa.accept_19_15_1_2_1_6894 72 77 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 287
  (Polychromatic418967fa.accept_19_14_1_2_1_11172 71 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 287 7 10 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 287 (Polychromatic418967fa.accept_20_8_17_7_1_12099 68 77
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 287 (accept_3_2 67 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 287 (accept_3_2 64 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  287 7 9 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 287 (accept_3_2 61 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 287 (Polychromatic418967fa.accept_20_19_17_7_1_6299 59 77
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 287 (accept_3_2 58 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 287 7 8 11 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 287 (accept_3_2 55
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 287 (Polychromatic418967fa.accept_19_15_1_2_1_6894 53 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 287 (accept_3_2 52 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 287 7 7 11 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 287 (accept_3_2 46 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 287 (Polychromatic418967fa.accept_19_7_1_2_1_9792 45 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123
  44 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 287 (accept_3_2 43
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 287 7 6 11 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 287
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 287 (accept_3_2 40 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 287 (accept_3_2 37 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 287 (Polychromatic418967fa.accept_20_16_17_7_1_7845 36 77 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 287 7 5 11 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 287 (accept_3_2 34 77 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 287
  (Polychromatic418967fa.accept_19_13_1_2_1_11154 32 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 287 (accept_3_2 31 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 287 7 4 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 287 (Polychromatic418967fa.accept_19_8_1_2_1_13747
  27 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 287 (accept_3_2 25 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 287 (Polychromatic418967fa.accept_17_6_9_15_1_3185 23 77 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 287 (accept_3_2 22 77 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 287 7 3 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 77 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 287 (accept_3_2 19 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 287
  (Polychromatic418967fa.accept_24_17_5_23_1_5724 17 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 287 (accept_3_2 16 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 287 7 2 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 287 (accept_3_2 13 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 287 (accept_3_2 10 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 287 (Polychromatic418967fa.accept_19_9_1_2_1_6839 9
  77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 77 287 7 1 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 77 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 287 (accept_3_2 4 77 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 287 (accept_3_2 1 77 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 287 (allA_of_3_0 76 76
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 287 (allA_succ_of_accept 74 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 287 (accept_3_2 73 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 71 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 287 (accept_3_2 70 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 287 (accept_3_2 67 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 287 (Polychromatic418967fa.accept_19_9_18_2_1_8383 66 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 287 (accept_3_2 64 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 287 (accept_3_2 61 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 287 (accept_3_2 58 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 287 (accept_3_2 55 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 287 (accept_3_2 52 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 287 (accept_3_2 49 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 287 (accept_3_2 46 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 287 (accept_3_2 43 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 287 (accept_3_2 40 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 287 (accept_3_2 37 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 287 (accept_3_2 34 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 287 (accept_3_2 31 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 287 (accept_3_2 28 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 287 (Polychromatic418967fa.accept_21_6_12_14_1_5704 27 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 287 (accept_3_2 25 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 287 (accept_3_2 22 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 287 (accept_3_2 19 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 287 (accept_3_2 16 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 287 (accept_3_2 13 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 287 (accept_3_2 10 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 287 (accept_3_2 7 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 287 (accept_3_2 4 75 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 75 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 287 (accept_3_2 1 75 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 287 (allA_succ_of_accept
  73 74 287 (accept_3_2 73 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 287 (accept_3_2 70 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 287 (accept_3_2 67 74
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 287 (accept_3_2 64 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 287 (Polychromatic418967fa.accept_10_2_4_7_1_352
  62 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 287 (accept_3_2 61
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 287 (accept_3_2 58 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 287 (accept_3_2 55
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 287
  (Polychromatic418967fa.accept_13_2_9_1_1_67 54 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 287 (accept_3_2 52 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 287 (accept_3_2 49 74
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 287 (accept_3_2 46 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 287 (accept_3_2 43
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 287 (accept_3_2 40 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214
  38 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 287 (accept_3_2 37
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 287
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 287 (accept_3_2 34 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 287 (accept_3_2 31 74
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 287 (accept_3_2 28 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  26 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 287 (accept_3_2 25
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 287 (accept_3_2 22 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 287 (accept_3_2 19
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 287 (accept_3_2 16 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 287 (accept_3_2 13 74
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 287 (accept_3_2 10 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 287 (accept_3_2 7 74 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 287 (accept_3_2 4 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 287 (accept_3_2 1 74 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  287 (allA_of_3_0 73 73 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 287 (allA_succ_of_accept 71 72 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 287 (accept_3_2 70 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 68 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 287 (accept_3_2 67 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 66 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 65 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 287 (accept_3_2 64 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 287 (accept_3_2 61 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 287 (accept_3_2 58 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 287 (Polychromatic418967fa.accept_16_9_8_15_1_5095 57 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 287 (Polychromatic418967fa.accept_19_18_15_2_1_11128 56 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 287 (accept_3_2 55 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 72 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 287
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 287 (accept_3_2 52 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 287 (accept_3_2 49 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 72 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 287
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 287 (accept_3_2 46 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 287 (accept_3_2 43 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 287
  (Polychromatic418967fa.accept_16_9_8_15_1_5095 41 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 287 (accept_3_2 40 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 287 (accept_3_2 37 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 287 (accept_3_2 34 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 287 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 287 (accept_3_2 31 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 287 (Polychromatic418967fa.accept_19_11_15_2_1_4096 30 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 287 (accept_3_2 28 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 287 (accept_3_2 25 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 72 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 287
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 287 (accept_3_2 22 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 287 (accept_3_2 19 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 72 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 287
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 287 (accept_3_2 16 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 287 (accept_3_2 13 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 287 (accept_3_2 10 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 287 (accept_3_2 7 72 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 72 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 287 (accept_3_2 4 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  287 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 72 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 287 (Polychromatic418967fa.accept_17_2_4_15_1_5451 2 72 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 287 (accept_3_2 1 72 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 287
  (allA_succ_of_accept 70 71 287 (accept_3_2 70 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 69 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 68 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 287 (accept_3_2 67 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 287 (accept_3_2 64 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 287 (Polychromatic418967fa.accept_17_12_3_15_1_5476 63 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 287 (Polychromatic418967fa.accept_14_6_1_7_1_2775 62 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 287 (accept_3_2 61 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 287
  (Polychromatic418967fa.accept_13_7_6_1_1_368 59 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 287 (accept_3_2 58 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 57 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 287 (accept_3_2 55 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 287
  (Polychromatic418967fa.accept_21_11_8_14_1_10515 53 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 71 287 (accept_3_2 52 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 71 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 51 71 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 71 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 287 (accept_3_2 49 71 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902
  48 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 287 (accept_3_2 46 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 287 (Polychromatic418967fa.accept_19_7_14_2_1_4095 45 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 287 (accept_3_2 43 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 287
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 287 (accept_3_2 40 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 287 (Polychromatic418967fa.accept_16_6_7_15_1_1942 38 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 287 (accept_3_2 37 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 287
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 287 (accept_3_2 34 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 287 (Polychromatic418967fa.accept_21_11_8_14_1_10515 32 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 287 (accept_3_2 31 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 287 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 71
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 287 (accept_3_2 28 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 287 (accept_3_2 25 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 287
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 23 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 287 (accept_3_2 22 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 287 (accept_3_2 19 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 287 (accept_3_2 16 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 287 (accept_3_2 13 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 287 (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 287
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 287 (accept_3_2 10 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 287 (accept_3_2 7 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 71 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 287 (accept_3_2 4 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 71 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 287 (accept_3_2 1 71 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 287 (allA_of_3_0 70 70 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 287
  (allA_succ_of_accept 68 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 287 (accept_3_2 67 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65
  69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 287 (accept_3_2 64 69
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 287
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 287 (accept_3_2 61 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 287 (accept_3_2 58 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  69 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 287 (accept_3_2 55 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 287 (accept_3_2 52 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 287 (accept_3_2 49 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 287 (accept_3_2 46 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 287 (accept_3_2 43 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 287 (accept_3_2 40 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 287 (accept_3_2 37 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 287 (accept_3_2 34 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 287 (accept_3_2 31 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 287 (accept_3_2 28 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 287 (accept_3_2 25 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 287 (accept_3_2 22 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 287 (accept_3_2 19 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 287
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 287 (accept_3_2 16 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 287 (accept_3_2 13 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 287 (accept_3_2 10 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 287 (accept_3_2 7 69 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 287 (accept_3_2 4 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 287 (accept_3_2 1 69 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 287
  (allA_succ_of_accept 67 68 287 (accept_3_2 67 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 287 (accept_3_2 64 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 287 (accept_3_2 61 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 287 (accept_3_2 58 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 287 (accept_3_2 55 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 287 (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 287 (accept_3_2 52 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 287 (accept_3_2 49 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 287 (accept_3_2 46 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 287 (accept_3_2 43 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 287 (accept_3_2 40 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 287 (accept_3_2 37 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 287 (accept_3_2 34 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 287
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 287 (accept_3_2 31 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 287 (accept_3_2 28 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 287 (accept_3_2 25 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 287 (Polychromatic418967fa.accept_14_9_12_7_1_597 23 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 287 (accept_3_2 22 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 287 (accept_3_2 19 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 287 (accept_3_2 16 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 287 (accept_3_2 13 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 287 (accept_3_2 10 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 287
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 287 (accept_3_2 7 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 68 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 287 (accept_3_2 4 68 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 287 (accept_3_2 1 68 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 287 (allA_of_3_0 67 67 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 287 (allA_succ_of_accept 65 66 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 287 (accept_3_2 64 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 287 (Polychromatic418967fa.accept_26_10_14_1_1_17618 62 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 287 (accept_3_2 61 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 287 (accept_3_2 58 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 287 (accept_3_2 55 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 287 (Polychromatic418967fa.accept_21_12_3_14_1_10498 54 66 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 287 (accept_3_2 52 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 287 (accept_3_2 49 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 48 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 287 (accept_3_2 46 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 287 (Polychromatic418967fa.accept_16_12_2_15_1_490 44 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 287 (accept_3_2 43 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 287 (accept_3_2 40 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 287 (accept_3_2 37 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 287 (Polychromatic418967fa.accept_19_17_9_2_1_12492 36 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 287
  (Polychromatic418967fa.accept_16_3_2_15_1_7367 35 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 287 (accept_3_2 34 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 287 (accept_3_2 31 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 287 (Polychromatic418967fa.accept_19_11_9_2_1_1729 30 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 287 (accept_3_2 28 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 287 (accept_3_2 25 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 287 (accept_3_2 22 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 287 (accept_3_2 19 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 287 (accept_3_2 16 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 287 (accept_3_2 13 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 66 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 287 (accept_3_2 10 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 66 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 287 (accept_3_2 7 66 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 287 (accept_3_2 4 66 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3
  66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 287 (accept_3_2 1 66 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 287 (allA_succ_of_accept 64 65 287
  (accept_3_2 64 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 287 (accept_3_2 61 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59
  65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 287 (accept_3_2 58 65
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 287 (accept_3_2 55 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 287 (Polychromatic418967fa.accept_10_3_5_7_1_330
  53 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 287 (accept_3_2 52
  65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 287 (accept_3_2 49 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 287 (Polychromatic418967fa.accept_14_5_9_7_1_590
  47 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 287 (accept_3_2 46
  65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 287
  (Polychromatic418967fa.accept_21_3_2_14_1_7235 45 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 287 (Polychromatic418967fa.accept_14_2_9_7_1_5633 44 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 287 (accept_3_2 43 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 287 (accept_3_2 40 65
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 287 (accept_3_2 37 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 287 (Polychromatic418967fa.accept_22_14_21_1_1_17617 36 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 287
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 287 (accept_3_2 34 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 287 (accept_3_2 31 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 287 (accept_3_2 28 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 287 (accept_3_2 25 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 287 (accept_3_2 22 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 287 (accept_3_2 19 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 287
  (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 287 (accept_3_2 16 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 287 (accept_3_2 13 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 287 (accept_3_2 10 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 287 (accept_3_2 7 65 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 287 (accept_3_2 4 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 287 (accept_3_2 1 65 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 287
  (allA_of_3_0 64 64 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 287 (allA_succ_of_accept 62 63 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 287 (accept_3_2 61 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 287 (accept_3_2 58 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 287 7 8 9 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 287 (accept_3_2 55 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 287
  (Polychromatic418967fa.accept_19_15_6_2_1_6865 53 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 287 (accept_3_2 52 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 287 7 7 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  48 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 287 (accept_3_2 46 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  63 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 287 (accept_3_2 43 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 287 7 6 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 63 287 (Polychromatic418967fa.accept_19_3_6_2_1_6910 41 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 287 (accept_3_2 40 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 287 (Polychromatic418967fa.accept_19_1_6_2_1_8341 39 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 287 (accept_3_2 37 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 63 287 7 5 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 63 287 (accept_3_2 34 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 287 (accept_3_2 31 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 287
  (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 63 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 287 7 4 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 287 (accept_3_2 25 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 287 (accept_3_2 22 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 287 7 3 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 287 (accept_3_2 19 63 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 287
  (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 287 (Polychromatic418967fa.accept_25_17_13_12_1_17616 17 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 287 (accept_3_2 16 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 287 7 2 9 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 287 (accept_3_2 13 63 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 287
  (Polychromatic418967fa.accept_22_11_19_1_1_8415 11 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 287 (accept_3_2 10 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 287 7 1 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6
  63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 287 (accept_3_2 4 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 63 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 63 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 287 (accept_3_2 1 63 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 63 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 287
  (allA_succ_of_accept 61 62 287 (accept_3_2 61 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  62 287 (Polychromatic418967fa.accept_19_3_5_2_1_4103 60 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 62 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 287 (accept_3_2 58 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 287 (accept_3_2 55 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 287 (accept_3_2 52 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 287 (accept_3_2 49 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 287 (Polychromatic418967fa.accept_17_13_11_15_1_5556 47 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 287 (accept_3_2 46 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 287 (accept_3_2 43 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 42 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 287 (accept_3_2 40 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 287
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 38 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 287 (accept_3_2 37 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 287 (accept_3_2 34 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 287 (accept_3_2 31 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 287 (accept_3_2 28 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 287
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 62 287 (accept_3_2 25 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 62 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 62 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 287 (Polychromatic418967fa.accept_16_7_14_15_1_2932 23 62
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 287 (accept_3_2 22 62 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 287 (accept_3_2 19 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 287 (Polychromatic418967fa.accept_19_18_5_2_1_8352 18 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 287 (accept_3_2 16 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 287 (accept_3_2 13 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 287 (Polychromatic418967fa.accept_20_12_2_7_1_4788 12 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 287 (accept_3_2 10 62 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 287 (accept_3_2 7 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  287 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 287 (accept_3_2 4 62 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754
  2 62 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 287 (accept_3_2 1 62
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 287 (allA_of_3_0 61 61 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 287 (allA_succ_of_accept 59 60 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 287 (accept_3_2 58 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 287 (accept_3_2 55 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 287 (Polychromatic418967fa.accept_19_16_3_2_1_6964 54 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 287
  (Polychromatic418967fa.accept_14_11_4_7_1_609 53 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 287 (accept_3_2 52 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 287 (accept_3_2 49 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 287 (accept_3_2 46 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 287 (accept_3_2 43 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 287 (Polychromatic418967fa.accept_24_18_12_23_1_12692 42 60 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 287 (accept_3_2 40 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 287 (accept_3_2 37 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 287 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 287 (accept_3_2 34 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 287 (accept_3_2 31 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 287 (accept_3_2 28 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 287 (Polychromatic418967fa.accept_21_5_18_14_1_2793 26 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 287 (accept_3_2 25 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 60
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 287 (accept_3_2 22 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 287 (accept_3_2 19 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 287 (accept_3_2 16 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 287 (accept_3_2 13 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 287 (accept_3_2 10 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 287 (accept_3_2 7 60 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 60 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 287 (accept_3_2 4 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 287 (accept_3_2 1 60 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 287
  (allA_succ_of_accept 58 59 287 (accept_3_2 58 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 287 (accept_3_2 55 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 287 (Polychromatic418967fa.accept_26_2_7_1_1_17615 54 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 287
  (Polychromatic418967fa.accept_14_11_3_7_1_604 53 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 287 (accept_3_2 52 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 287 (accept_3_2 49 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 287 (accept_3_2 46 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 287 (accept_3_2 43 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 287 (accept_3_2 40 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 287 (accept_3_2 37 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 287 (accept_3_2 34 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 287 (accept_3_2 31 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 287 (accept_3_2 28 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 287 (Polychromatic418967fa.accept_16_10_11_15_1_6302 26 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 287 (accept_3_2 25 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 287
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 287 (accept_3_2 22 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 287 (accept_3_2 19 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 287 (accept_3_2 16 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 287 (Polychromatic418967fa.accept_22_14_15_1_1_17614 14 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 287 (accept_3_2 13 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 287 (accept_3_2 10 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 287 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 287 (accept_3_2 7 59 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 287 (accept_3_2 4 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 287 (accept_3_2 1 59 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 287 (allA_of_3_0
  58 58 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 287 (allA_succ_of_accept 56 57 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 287 (accept_3_2 55 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 287 (Polychromatic418967fa.accept_22_9_13_1_1_8400 53 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 287 (accept_3_2 52 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 287 (accept_3_2 49 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 287 (accept_3_2 46 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 287 (accept_3_2 43 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 287 (accept_3_2 40 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 287 (accept_3_2 37 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 287 (accept_3_2 34 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 287 (accept_3_2 31 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 287 (accept_3_2 28 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 287 (accept_3_2 25 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 287 (accept_3_2 22 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 287 (accept_3_2 19 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 287 (accept_3_2 16 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 287 (accept_3_2 13 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 287 (accept_3_2 10 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 57 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 287 (accept_3_2 7 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 57 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 287 (accept_3_2 4 57 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 57 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 287 (accept_3_2 1 57 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 287 (allA_succ_of_accept 55 56 287 (accept_3_2 55 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 287 (accept_3_2 52 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 56 287 7 7 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 56 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 287 (Polychromatic418967fa.accept_17_13_5_15_1_8103 47 56
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 287 (accept_3_2 46 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 287
  (Polychromatic418967fa.accept_13_5_4_1_1_364 44 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 287 (accept_3_2 43 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  287 7 6 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 56 287 (accept_3_2 40 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 56 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 287 (accept_3_2 37 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  36 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 287 7 5 8 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 287 (accept_3_2 34
  56 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 287 (accept_3_2 31 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 287 (Polychromatic418967fa.accept_13_3_4_1_1_363
  29 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 287 7 4 8 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 56 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 287 (accept_3_2 25 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 56 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 287 (accept_3_2 22 56
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56 287 7 3 8 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 56 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 287 (accept_3_2 19 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 56 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 287 (accept_3_2 16 56 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 287 7 2 8 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 287 (accept_3_2 13 56 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 287 (accept_3_2 10 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  56 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 56 287 (Polychromatic418967fa.accept_18_8_2_17_1_4782 8 56 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 287 7 1 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 287 (accept_3_2 4 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 56 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 287 (accept_3_2 1 56 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 287 (allA_of_3_0 55
  55 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 287 (allA_succ_of_accept 53 54 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 287 (accept_3_2 52 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 287 (Polychromatic418967fa.accept_21_8_12_14_1_10464 50 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 287 (accept_3_2 49 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 54 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 287
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 47 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 287 (accept_3_2 46 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 287 (accept_3_2 43 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 287 (accept_3_2 40 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 287 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 38 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 287 (accept_3_2 37 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 287 (Polychromatic418967fa.accept_19_17_16_2_1_8390 36 54
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 287
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 287 (accept_3_2 34 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 287 (accept_3_2 31 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 30 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 287 (accept_3_2 28 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 287 (Polychromatic418967fa.accept_21_6_12_14_1_5704 27 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 287 (accept_3_2 25 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 54
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 287 (accept_3_2 22 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 287 (accept_3_2 19 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 287 (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 287 (accept_3_2 16 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 287 (Polychromatic418967fa.accept_21_15_12_14_1_7232 15 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 287 (Polychromatic418967fa.accept_17_14_3_15_1_5449 14 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 287 (accept_3_2 13 54 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 287 (accept_3_2 10 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 54 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 54 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 287 (accept_3_2 7 54 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 54 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 54 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 287 (accept_3_2 4 54 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 3
  54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 287 (accept_3_2 1 54 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 287 (allA_succ_of_accept 52 53 287 (accept_3_2
  52 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 287
  (Polychromatic418967fa.accept_15_6_8_2_1_104 51 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 287 (accept_3_2 49 53 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 287 (Polychromatic418967fa.accept_21_6_11_14_1_11812 48 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 287
  (Polychromatic418967fa.accept_17_13_2_15_1_2151 47 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 287 (accept_3_2 46 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 287 (accept_3_2 43 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 287
  (Polychromatic418967fa.accept_17_7_2_15_1_1255 41 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 287 (accept_3_2 40 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 287 (accept_3_2 37 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 287 (accept_3_2 34 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 287 (accept_3_2 31 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 287
  (Polychromatic418967fa.accept_21_8_11_14_1_5665 29 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 287 (accept_3_2 28 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 287 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 287 (accept_3_2 25 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 287
  (Polychromatic418967fa.accept_21_2_11_14_1_11805 23 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 53 287 (accept_3_2 22 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 53 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 53 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 287 (Polychromatic418967fa.accept_16_4_5_15_1_5083 20 53
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 287 (accept_3_2 19 53 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 287 (accept_3_2 16 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 287 (accept_3_2 13 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 287 (Polychromatic418967fa.accept_21_12_11_14_1_7239 12 53 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 287
  (Polychromatic418967fa.accept_19_11_15_2_1_4096 11 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 287 (accept_3_2 10 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 287 (Polychromatic418967fa.accept_19_8_15_2_1_6961 8 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 287 (accept_3_2 7 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 287 (accept_3_2 4 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 53 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 287 (accept_3_2 1 53 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 287))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 287
  (allA_of_3_0 52 52 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 287 (allA_succ_of_accept 50 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 287 (accept_3_2 49 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 287 (accept_3_2 46 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 287 (accept_3_2 43 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 287 (accept_3_2 40 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 287 (accept_3_2 37 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 287 (Polychromatic418967fa.accept_19_16_13_2_1_6920 35 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 287 (accept_3_2 34 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 287 (accept_3_2 31 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 287 (accept_3_2 28 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 287 (accept_3_2 25 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 287 (accept_3_2 22 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 287 (accept_3_2 19 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 287 (accept_3_2 16 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 287 (accept_3_2 13 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 287 (accept_3_2 10 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 287 (accept_3_2 7 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  287 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 51 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 287 (accept_3_2 4 51 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 287 (accept_3_2 1 51 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 287)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 287 (allA_succ_of_accept 49 50 287 (accept_3_2 49 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 287 (accept_3_2 46 50 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 287 (accept_3_2 43 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 287 (accept_3_2 40 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 287 (accept_3_2 37 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 287 (accept_3_2 34 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 287 (accept_3_2 31 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 287 (accept_3_2 28 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 26 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 287 (accept_3_2 25 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 287 (accept_3_2 22 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 287 (accept_3_2 19 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 287 (accept_3_2 16 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 287 (accept_3_2 13 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 287 (accept_3_2 10 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 287 (accept_3_2 7 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 287 (accept_3_2 4 50 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 287 (accept_3_2 1 50 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 287)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 287 (allA_of_3_0 49 49 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 287 (allA_succ_of_accept 47 48
  287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 287 (accept_3_2 46 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 287 (accept_3_2 43 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 287 (accept_3_2 40 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 287 (accept_3_2 37 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 287 (accept_3_2 34 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 287 (accept_3_2 31 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 287 (accept_3_2 28 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 287 (Polychromatic418967fa.accept_25_1_23_12_1_17613 26 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 287 (accept_3_2 25 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 287 (accept_3_2 22 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 287 (accept_3_2 19 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 287
  (Polychromatic418967fa.accept_19_17_10_2_1_9793 17 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 287 (accept_3_2 16 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 287 (accept_3_2 13 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 287 (accept_3_2 10 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 287 (accept_3_2 7 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 287 (accept_3_2 4 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  287 (Polychromatic418967fa.accept_17_3_14_15_1_5502 3 48 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 287 (accept_3_2 1 48 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 287)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 287
  (allA_succ_of_accept 46 47 287 (accept_3_2 46 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 287 (accept_3_2 43 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 287 (accept_3_2 40 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 38 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 287 (accept_3_2 37 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 287 (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 287 (accept_3_2 34 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 287 (accept_3_2 31 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 287
  (Polychromatic418967fa.accept_21_8_5_14_1_5660 29 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 287 (accept_3_2 28 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 287 (Polychromatic418967fa.accept_22_5_3_1_1_13158 27 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 287 (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 287 (accept_3_2 25 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 287 (accept_3_2 22 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 287 (accept_3_2 19 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 287
  (Polychromatic418967fa.accept_19_17_9_2_1_12492 17 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 287 (accept_3_2 16 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 287 (accept_3_2 13 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 287
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 287 (accept_3_2 10 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 287 (Polychromatic418967fa.accept_17_8_13_15_1_2143 8 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 287 (accept_3_2 7 47 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 287 (accept_3_2 4 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 47 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 287 (accept_3_2 1 47 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 287))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 287 (allA_of_3_0 46 46 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 287 (allA_succ_of_accept 44 45 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 287 (accept_3_2 43 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 287 (accept_3_2 40 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 287 (accept_3_2 37 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 287 (Polychromatic418967fa.accept_19_17_7_2_1_11110 36 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 287 (accept_3_2 34 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 287 (accept_3_2 31 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 287 (accept_3_2 28 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 287 (accept_3_2 25 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 287 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 287 (accept_3_2 22 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 287 (accept_3_2 19 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 287 (Polychromatic418967fa.accept_19_17_7_2_1_11110 17 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 287 (accept_3_2 16 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 45 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 287 (accept_3_2 13 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 287 (accept_3_2 10 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 45 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 287 (accept_3_2 7 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 45 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 287 (accept_3_2 4 45 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 287 (accept_3_2 1 45 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 287))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  287 (allA_succ_of_accept 43 44 287 (accept_3_2 43 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 287 (accept_3_2 40 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 287 (accept_3_2 37 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 287 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 287 (accept_3_2 34 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 287 (accept_3_2 31 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 287 (accept_3_2 28 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 287 (accept_3_2 25 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 287 (accept_3_2 22 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 287 (accept_3_2 19 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 287 (accept_3_2 16 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 287 (accept_3_2 13 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 287 (accept_3_2 10 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 287 (accept_3_2 7 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  287 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 287 (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 44 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 287 (accept_3_2 4 44 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  44 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 287 (accept_3_2 1 44 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 287)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  287 (allA_of_3_0 43 43 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 287 (allA_succ_of_accept 41 42 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 287 (accept_3_2 40 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 287 (accept_3_2 37 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 42 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 42 287 7 5 6 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 287 (accept_3_2 34 42 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 287 (accept_3_2 31 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  42 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 42 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 287 7 4 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 287
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 287 (Polychromatic418967fa.accept_19_7_4_2_1_6959 26 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 287 (accept_3_2 25 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 287 (accept_3_2 22 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42
  287 7 3 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  42 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 42 287 (accept_3_2 19 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 42 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 287 (accept_3_2 16 42 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 287 (Polychromatic418967fa.accept_10_5_2_7_1_345
  15 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 287 7 2 6 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 287 (accept_3_2 13
  42 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 287 (accept_3_2 10 42 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 287 (Polychromatic418967fa.accept_22_8_20_1_1_17612
  8 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 287 7 1 6 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 287 (accept_3_2 4 42 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  42 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 287 (accept_3_2 1 42 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 287)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 287
  (allA_succ_of_accept 40 41 287 (accept_3_2 40 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 287 (accept_3_2 37 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 287
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 287 (accept_3_2 34 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 287 (accept_3_2 31 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 287 (accept_3_2 28 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 287 (Polychromatic418967fa.accept_21_6_20_14_1_8837 27 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 287 (accept_3_2 25 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 287
  (Polychromatic418967fa.accept_21_2_20_14_1_5649 23 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 287 (accept_3_2 22 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 287 (accept_3_2 19 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 287
  (Polychromatic418967fa.accept_19_17_3_2_1_1725 17 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 287 (accept_3_2 16 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 287 (accept_3_2 13 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 287 (accept_3_2 10 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 287 (accept_3_2 7 41 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 287 (accept_3_2 4 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 287 (accept_3_2 1 41 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 287))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 287 (allA_of_3_0 40 40 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 287 (allA_succ_of_accept 38 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 287 (accept_3_2 37 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 287 (Polychromatic418967fa.accept_21_15_18_14_1_5632 36 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 287 (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 287 (accept_3_2 34 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 287 (accept_3_2 31 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 287 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 287 (accept_3_2 28 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 287 (accept_3_2 25 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 287 (accept_3_2 22 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 287 (accept_3_2 19 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 287 (accept_3_2 16 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 287 (accept_3_2 13 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 287 (accept_3_2 10 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 287 (accept_3_2 7 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 287 (accept_3_2 4 39 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 39 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 287 (accept_3_2 1 39 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 287))))))))))))))))))))))))))))))))))))))) (allB_succ 38 287
  (allA_succ_of_accept 37 38 287 (accept_3_2 37 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 287 (accept_3_2 34 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 287 (accept_3_2 31 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 287 (accept_3_2 28 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 287 (accept_3_2 25 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 287 (accept_3_2 22 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 287 (accept_3_2 19 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 287 (accept_3_2 16 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 287 (accept_3_2 13 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 287 (accept_3_2 10 38 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 287 (accept_3_2 7 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 287 (accept_3_2 4 38 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 2
  38 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 287 (accept_3_2 1 38 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 287)))))))))))))))))))))))))))))))))))))) (allB_succ 37 287
  (allA_of_3_0 37 37 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 287 (allA_succ_of_accept 35 36 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 287 (accept_3_2 34 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 287 (Polychromatic418967fa.accept_22_10_14_1_1_13148 32 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 287 (accept_3_2 31 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 36
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 287
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 29 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 287 (accept_3_2 28 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 287 (accept_3_2 25 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 36 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 287 (accept_3_2 22 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 287 (accept_3_2 19 36 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 287 (Polychromatic418967fa.accept_21_18_15_14_1_8871 18 36 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 287
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 287 (accept_3_2 16 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 287 (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 287 (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 287 (accept_3_2 13 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 36
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 287 (accept_3_2 10 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 36 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 287 (accept_3_2 7 36 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 36 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 287
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 287 (accept_3_2 4 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 36 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 36 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 287 (accept_3_2 1 36 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 287)))))))))))))))))))))))))))))))))))) (allB_succ 35 287 (allA_succ_of_accept 34 35 287
  (accept_3_2 34 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 287 (accept_3_2 31 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 287 (Polychromatic418967fa.accept_19_11_16_2_1_9759 30 35 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 287 7 4 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 35 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 287 (accept_3_2 25 35 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407
  24 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 287 (accept_3_2 22 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  287 7 3 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 287 (accept_3_2 19 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 287 (Polychromatic418967fa.accept_19_17_16_2_1_8390 17 35
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 287 (accept_3_2 16 35 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 15
  35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 287 7 2 5 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 287 (accept_3_2 13
  35 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 287 (accept_3_2 10 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 35 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 8
  35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 287 7 1 5 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 287
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 287 (accept_3_2 4 35 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 35 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2
  35 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 287 (accept_3_2 1 35 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 287))))))))))))))))))))))))))))))))))) (allB_succ 34 287
  (allA_of_3_0 34 34 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 287 (allA_succ_of_accept 32 33 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 287 (accept_3_2 31 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 287 (accept_3_2 28 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 287 (accept_3_2 25 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 287 (accept_3_2 22 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 287 (accept_3_2 19 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 287 (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 33 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 287 (accept_3_2 16 33 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 33 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 287 (accept_3_2 13 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 287 (accept_3_2 10 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 33 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 287 (accept_3_2 7 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 287 (accept_3_2 4 33 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 287 (accept_3_2 1 33 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 287))))))))))))))))))))))))))))))))) (allB_succ 32 287
  (allA_succ_of_accept 31 32 287 (accept_3_2 31 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 287 (accept_3_2 28 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 287 (accept_3_2 25 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 287 (Polychromatic418967fa.accept_21_2_11_14_1_11805 23 32 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 287 (accept_3_2 22 32 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 287 (accept_3_2 19 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 287 (accept_3_2 16 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 287 (accept_3_2 13 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 287 (accept_3_2 10 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 287 (accept_3_2 7 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 32 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 32 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 287 (accept_3_2 4 32 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 287 (accept_3_2 1 32 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 287)))))))))))))))))))))))))))))))) (allB_succ 31 287
  (allA_of_3_0 31 31 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 287 (allA_succ_of_accept 29 30 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 287 (accept_3_2 28 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 287 (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 287 (accept_3_2 25 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 287 (accept_3_2 22 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 287 (accept_3_2 19 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 30 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 287 (accept_3_2 16 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 287 (accept_3_2 13 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 30 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 287 (accept_3_2 10 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 287 (Polychromatic418967fa.accept_17_8_13_15_1_2143 8 30 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 287 (accept_3_2 7 30 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 287 (accept_3_2 4 30 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 3
  30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 287 (accept_3_2 1 30 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  287)))))))))))))))))))))))))))))) (allB_succ 29 287 (allA_succ_of_accept 28 29 287 (accept_3_2 28 29 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 29
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 287 (accept_3_2 25 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 29 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 287 (accept_3_2 22 29 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 287 (accept_3_2 19 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 29 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 287 (accept_3_2 16 29 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 287 (accept_3_2 13 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 29 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 287 (accept_3_2 10 29 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 287 (Polychromatic418967fa.accept_27_9_2_17_1_17611 9 29 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 287
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 287 (accept_3_2 7 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 287 (accept_3_2 4 29 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 287 (accept_3_2 1 29 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 287))))))))))))))))))))))))))))) (allB_succ 28 287 (allA_of_3_0
  28 28 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 287 (allA_succ_of_accept 26 27 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 287 (accept_3_2 25 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 287 (Polychromatic418967fa.accept_19_5_8_2_1_1707 24 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 27 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 287 (accept_3_2 22 27 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 287 (accept_3_2 19 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 27 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 287 (accept_3_2 16 27 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 27 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 287 (accept_3_2 13 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 287 (Polychromatic418967fa.accept_19_11_8_2_1_2847 11 27 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 287 (accept_3_2 10 27 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 287 (accept_3_2 7 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  287 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 27 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 287 (accept_3_2 4 27 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 27 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 287 (accept_3_2 1 27 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 287))))))))))))))))))))))))))) (allB_succ 26 287
  (allA_succ_of_accept 25 26 287 (accept_3_2 25 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 24 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 287 (accept_3_2 22 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 287 (accept_3_2 19 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 287 (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 287 (accept_3_2 16 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 287
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 26 287 (accept_3_2 13 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 26 287 (Polychromatic418967fa.accept_20_12_6_7_1_7875 12 26 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 26 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 287 (accept_3_2 10 26 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 287 (accept_3_2 7 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 26 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 287 (accept_3_2 4 26 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 287
  (Polychromatic418967fa.accept_14_2_12_7_1_617 2 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 287 (accept_3_2 1 26 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  287)))))))))))))))))))))))))) (allB_succ 25 287 (allA_of_3_0 25 25 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 287 (allA_succ_of_accept 23 24 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 287 (accept_3_2 22 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 287 (accept_3_2 19 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 287 (accept_3_2 16 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 24
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 287 (accept_3_2 13 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 287 (accept_3_2 10 24 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 287 (accept_3_2 7 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 6 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 287 (accept_3_2 4 24 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 287 (accept_3_2 1 24 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  287)))))))))))))))))))))))) (allB_succ 23 287 (allA_succ_of_accept 22 23 287 (accept_3_2 22 23 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 287 (accept_3_2 19 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 287 (Polychromatic418967fa.accept_19_18_4_2_1_2841 18 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 23 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 287 (accept_3_2 16 23 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 287 (accept_3_2 13 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 287 (accept_3_2 10 23 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 23 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 287
  (Polychromatic418967fa.accept_16_8_7_15_1_6339 8 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 287 (accept_3_2 7 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 287 (accept_3_2 4 23 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 287 (accept_3_2 1 23 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 287))))))))))))))))))))))) (allB_succ 22 287 (allA_of_3_0 22 22
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 287 (allA_succ_of_accept 20 21 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 287 (accept_3_2 19 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 21 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 287 (accept_3_2 16 21 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 21 287 7 2 3 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 287 (accept_3_2 13 21 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 287 (Polychromatic418967fa.accept_13_12_8_1_1_825
  12 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 287 (accept_3_2 10 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 287 7 1 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 287 (accept_3_2 4 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 287 (accept_3_2 1 21 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 287))))))))))))))))))))) (allB_succ 20 287 (allA_succ_of_accept 19 20 287
  (accept_3_2 19 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 287
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 287 (Polychromatic418967fa.accept_21_17_20_14_1_11808 17 20 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 287 (accept_3_2 16 20 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 287 (accept_3_2 13 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 20 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 287 (accept_3_2 10 20 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 287
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 287 (accept_3_2 7 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 287 (accept_3_2 4 20 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  20 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 287 (accept_3_2 1 20 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 287)))))))))))))))))))) (allB_succ 19 287 (allA_of_3_0 19 19 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 287 (allA_succ_of_accept 17 18 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 287 (accept_3_2 16 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  18 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 18 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 18 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 287 (accept_3_2 13 18 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 18
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 287
  (Polychromatic418967fa.accept_14_11_4_7_1_609 11 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 287 (accept_3_2 10 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  18 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 18 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 287 (accept_3_2 7 18 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 18 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 287 (accept_3_2 4 18 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3
  18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 287
  (Polychromatic418967fa.accept_20_2_18_7_1_3394 2 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 287 (accept_3_2 1 18 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  287)))))))))))))))))) (allB_succ 17 287 (allA_succ_of_accept 16 17 287 (accept_3_2 16 17 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 287 (Polychromatic418967fa.accept_19_15_17_2_1_4097 15 17 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 287 (accept_3_2 13 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 287 (Polychromatic418967fa.accept_19_12_17_2_1_6888 12 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 17 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 287 (accept_3_2 10 17 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 287 (Polychromatic418967fa.accept_19_9_17_2_1_5428 9 17 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 287
  (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 287 (accept_3_2 7 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 17 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 287 (accept_3_2 4 17 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 17 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 287 (accept_3_2 1 17 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 287))))))))))))))))) (allB_succ 16 287 (allA_of_3_0 16 16 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 287 (allA_succ_of_accept 14 15 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 287 (accept_3_2 13 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 15 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 287 (accept_3_2 10 15 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 287 (accept_3_2 7 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 15 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 15 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 287 (accept_3_2 4 15 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 287 (accept_3_2 1 15 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  287))))))))))))))) (allB_succ 14 287 (allA_succ_of_accept 13 14 287 (accept_3_2 13 14 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  14 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 287 (accept_3_2 10 14
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  14 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 14 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 14 287 7 1 2 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 14 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 287 (accept_3_2 4 14 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 287 (accept_3_2 1 14 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  287)))))))))))))) (allB_succ 13 287 (allA_of_3_0 13 13 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 287
  (allA_succ_of_accept 11 12 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 287 (accept_3_2 10 12 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 12 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662
  8 12 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 287 (accept_3_2 7 12
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 287 (Polychromatic418967fa.accept_9_6_3_8_1_595
  6 12 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 287 (accept_3_2 4 12 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 12 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 287 (accept_3_2 1 12 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 287)))))))))))) (allB_succ 11 287 (allA_succ_of_accept 10 11 287 (accept_3_2 10 11 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375
  9 11 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 11 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 287 (accept_3_2 7 11 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 287 (accept_3_2 4 11 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 11 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 287 (Polychromatic418967fa.accept_18_2_11_17_1_4773
  2 11 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 287 (accept_3_2 1 11
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 287))))))))))) (allB_succ 10 287 (allA_of_3_0 10 10 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 287 (allA_succ_of_accept 8 9 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 287 (accept_3_2 7 9 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 9 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 287 (accept_3_2 4 9 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 287 (accept_3_2 1 9 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 287))))))))) (allB_succ 8 287 (allA_succ_of_accept 7 8 287
  (accept_3_2 7 8 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 287
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 8 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 8 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 287 (accept_3_2 4 8 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 287 (accept_3_2 1 8 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 287)))))))) (allB_succ 7 287 (allA_of_3_0 7 7 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 287 (allA_succ_of_accept 5 6 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 287 (accept_3_2 4 6 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 287 (accept_3_2 1 6 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 287)))))) (allB_succ 5 287 (allA_succ_of_accept 4 5 287 (accept_3_2 4 5 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 287 (accept_3_2 1 5 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 287)))))
  (allB_succ 4 287 (allA_of_3_0 4 4 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 287 (allA_succ_of_accept 2
  3 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 287 (accept_3_2 1 3 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 287)))
  (allB_succ 2 287 (allA_succ_of_accept 1 2 287 (accept_3_2 1 2 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  287)) (allB_two
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


