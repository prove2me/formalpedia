-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch233_Segment000
-- name    : Polychromatic418967fa_Branch233_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:37:08.416866+00:00
-- url     : https://prove2.me/theorems/c81d1bb0-e4c8-4b7c-a385-cdb5b21d4bad
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

def Polychromatic418967fa.branch_233_segment_000 : allB 123 233 :=
  allB_succ' 112 122 233 (Eq.refl Bool.true) (allA_succ_of_accept 111 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50
  111 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 122 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 110 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 122 233 (accept_3_2 109 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 122 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 108 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 122 233 (accept_3_2 106 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 122
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 122 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 104 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 122 233 (accept_3_2 103 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 122 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 122 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 122 233 (accept_3_2 100 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 122 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 122 233
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 122 233 (accept_3_2 97 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 122 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 122 233 (accept_3_2 94 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 122 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 92 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 122 233 (accept_3_2 91 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 122 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 122 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 122 233 (accept_3_2 88 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 122 233
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 86 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 122 233 (accept_3_2 85 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 122 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 122 233 (accept_3_2 82 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 122 233
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 122 233 (accept_3_2 79 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 122 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 122 233 (Polychromatic418967fa.accept_21_14_17_2_1_11069 77 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 122 233 (accept_3_2 76 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 122 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 122 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 122 233 (accept_3_2 73 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 122 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 122 233 (accept_3_2 70 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 122 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 122 233 (accept_3_2 67 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 122 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 122 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 233 (accept_3_2 64 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 233 (accept_3_2 61 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 233 (accept_3_2 58 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 233 (accept_3_2 55 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 53 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 233 (accept_3_2 52 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 233 (accept_3_2 49 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 233 (accept_3_2 46 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 233 (accept_3_2 43 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 233 (accept_3_2 40 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 233 (accept_3_2 37 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 233 (accept_3_2 34 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 233
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 233 (accept_3_2 31 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 233 (accept_3_2 28 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 233 (accept_3_2 25 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 233 (accept_3_2 22 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 233 (accept_3_2 19 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 233 (Polychromatic418967fa.accept_20_18_2_13_1_5265 18 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 233 (accept_3_2 16 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 233
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 233 (accept_3_2 13 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 233 (accept_3_2 10 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 233 (accept_3_2 7 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 233 (accept_3_2 4 122 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 233 (accept_3_2 1 122 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 121 233 (Eq.refl Bool.true) (allA_of_3_0 113 121 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 120 233 (Eq.refl Bool.true) (allA_succ_of_accept 113 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 113 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 120 233 (accept_3_2 112 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 120 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 120 233 (accept_3_2 109 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 120
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 120 233
  (Polychromatic418967fa.accept_22_19_10_13_1_7775 107 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 120 233 (accept_3_2 106 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 120 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 104 120
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 233 (accept_3_2 103 120
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 120 233
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 102 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 120 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 233 (accept_3_2 100 120 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 120 233 (Polychromatic418967fa.accept_14_1_8_9_1_1312 99 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 233
  (Polychromatic418967fa.accept_17_13_1_12_1_7893 98 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 120 233 (accept_3_2 97 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 120 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 233 (accept_3_2 94 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 233 (Polychromatic418967fa.accept_13_2_3_12_1_735
  93 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 233 (accept_3_2 91 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 89 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 233 (accept_3_2 88 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 120 233 (accept_3_2 85 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 120 233 (Polychromatic418967fa.accept_16_4_8_9_1_4639 84 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 233 (accept_3_2 82 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 233 (Polychromatic418967fa.accept_16_1_8_9_1_3462 81 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 233 (accept_3_2 79 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 233 (accept_3_2 76 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 233 (Polychromatic418967fa.accept_19_18_6_5_1_4321 75 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 233 (accept_3_2 73 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 233 (Polychromatic418967fa.accept_19_15_6_5_1_4356 72 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 233 (Polychromatic418967fa.accept_14_1_8_9_1_1312 71 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 233 (accept_3_2 70 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 233 (accept_3_2 67 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 233 (accept_3_2 64 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 233 (Polychromatic418967fa.accept_16_15_8_9_1_2563 63 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 233 (accept_3_2 61 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 233 (accept_3_2 58 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 233 (Polychromatic418967fa.accept_14_1_8_9_1_1312 57 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 233 (accept_3_2 55 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 233 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 233 (Polychromatic418967fa.accept_19_15_6_5_1_4356 53 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 233 (accept_3_2 52 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 233 (accept_3_2 49 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 233 (accept_3_2 46 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 233
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 233 (accept_3_2 43 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 233 (accept_3_2 40 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 233 (Polychromatic418967fa.accept_16_7_8_9_1_9427 39 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 233 (accept_3_2 37 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 233 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 233 (accept_3_2 34 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 233 (accept_3_2 31 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 233 (accept_3_2 28 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 233
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 26 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 233 (accept_3_2 25 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 233 (accept_3_2 22 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 233 (Polychromatic418967fa.accept_22_21_10_13_1_13924 21 120 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 233 (accept_3_2 19 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 233 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 233 (accept_3_2 16 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 233 (accept_3_2 13 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 233 (accept_3_2 10 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 233
  (Polychromatic418967fa.accept_21_8_15_2_1_4805 8 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 233 (accept_3_2 7 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 233 (accept_3_2 4 120 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 233 (accept_3_2 1 120 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 119 233 (Eq.refl Bool.true) (allA_succ_of_accept 114 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2
  114 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 119 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 119 233 (accept_3_2 112 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 119 233 (accept_3_2 109 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 119 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 108 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 233
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 107 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 119 233 (accept_3_2 106 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 105 119 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 233 (accept_3_2 103 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 119 233 (Polychromatic418967fa.accept_13_10_2_12_1_1332 101 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 233 (accept_3_2 100 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 99 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 233 (accept_3_2 97 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 233 (accept_3_2 94 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 92 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 233 (accept_3_2 91 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 233 (Polychromatic418967fa.accept_14_5_7_9_1_3828 89 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 233 (accept_3_2 88 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 233 (accept_3_2 85 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 83 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 233 (accept_3_2 82 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 80 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 233 (accept_3_2 79 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 233 (accept_3_2 76 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 233 (accept_3_2 73 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 233 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 233 (accept_3_2 70 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 233 (accept_3_2 67 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 233 (accept_3_2 64 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 233 (Polychromatic418967fa.accept_25_13_19_8_1_10561 63
  119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 233 (accept_3_2 61 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 233 (accept_3_2 58 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 233
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 233 (accept_3_2 55 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 233 (accept_3_2 52 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 233 (accept_3_2 49 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 233 (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 233 (accept_3_2 46 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 233
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 233 (accept_3_2 43 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 233 (accept_3_2 40 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 233 (accept_3_2 37 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 233 (accept_3_2 34 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 233 (accept_3_2 31 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 233 (accept_3_2 28 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 233 (accept_3_2 25 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 233 (accept_3_2 22 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 233 (accept_3_2 19 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 233 (accept_3_2 16 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 233 (accept_3_2 13 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 233 (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 233 (accept_3_2 10 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 119
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 233
  (Polychromatic418967fa.accept_16_8_7_9_1_7052 8 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 233 (accept_3_2 7 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 233 (accept_3_2 4 119 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 233 (accept_3_2 1 119 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 118 233 (Eq.refl Bool.true) (allA_of_3_0 116 118 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 117 233 (allA_succ_of_accept 116 117 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 233 (accept_3_2 115 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 114 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 233
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 113 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 233 (accept_3_2 112 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 111 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 233 (accept_3_2 109 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 233
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 107 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 117 233 (accept_3_2 106 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 117 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 233 (accept_3_2 103 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 102 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 117 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 233 (accept_3_2 100 117 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 117 233 (accept_3_2 97 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 117 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 233 (accept_3_2 94 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 93 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 233 (accept_3_2 91 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 233 (Polychromatic418967fa.accept_19_14_3_5_1_11347 90 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 233 (Polychromatic418967fa.accept_23_20_2_3_1_9112 89 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 233 (accept_3_2 88 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 117 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 233 (accept_3_2 85 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 117 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 117 233 (Polychromatic418967fa.accept_19_7_3_5_1_8585 83 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 233 (accept_3_2 82 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 117 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 233 (accept_3_2 79 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 78 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 233 (Polychromatic418967fa.accept_14_7_5_9_1_2911 77 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 233 (accept_3_2 76 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 233 (accept_3_2 73 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 233 (Polychromatic418967fa.accept_21_9_12_2_1_4781 72 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 233 (Polychromatic418967fa.accept_15_11_12_8_1_739 71 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 233 (accept_3_2 70 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 233 (Polychromatic418967fa.accept_17_1_15_12_1_7907 69 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 233 (accept_3_2 67 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 65 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 233 (accept_3_2 64 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 233 (accept_3_2 61 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 233 (accept_3_2 58 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 233 (Polychromatic418967fa.accept_27_3_9_17_1_13923 57 117 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 233 (accept_3_2 55 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 233 (accept_3_2 52 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 233 (accept_3_2 49 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 233 (Polychromatic418967fa.accept_23_1_2_3_1_13922 47 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 233 (accept_3_2 46 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 233 (accept_3_2 43 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 233 (Polychromatic418967fa.accept_15_11_12_8_1_739 41 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 233 (accept_3_2 40 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 117 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 233 (accept_3_2 37 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 233 (accept_3_2 34 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 233 (accept_3_2 31 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 233 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 233 (Polychromatic418967fa.accept_16_13_5_9_1_4682 29 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 233 (accept_3_2 28 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 233 (accept_3_2 25 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 233 (Polychromatic418967fa.accept_25_23_17_8_1_13921 23 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 233 (accept_3_2 22 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 233 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 117
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 233 (accept_3_2 19 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 233 (accept_3_2 16 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 233 (accept_3_2 13 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 233 (accept_3_2 10 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 233 (accept_3_2 7 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 233 (accept_3_2 4 117 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 233 (accept_3_2 1 117 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 233 (allA_succ_of_accept 115 116 233 (accept_3_2 115 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 114 116 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 233 (Polychromatic418967fa.accept_17_11_14_12_1_2995 113
  116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 233 (accept_3_2 112
  116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 110 116 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 233 (accept_3_2 109 116 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 107 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 233 (accept_3_2 106 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 104 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 233 (accept_3_2 103 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 102
  116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 101 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 116 233 (accept_3_2 100 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 98 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 233 (accept_3_2 97 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 116 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 95 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 116 233 (accept_3_2 94 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 116 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 92 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 116 233 (accept_3_2 91 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 116 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 116 233 (accept_3_2 88 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 116 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 86 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 116 233 (accept_3_2 85 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 116 233 (Polychromatic418967fa.accept_19_8_2_5_1_5678 84 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 116 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 116 233 (accept_3_2 82 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 116 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 80 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 116 233 (accept_3_2 79 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 116 233 (accept_3_2 76 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 116 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 74 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 116 233 (accept_3_2 73 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 116 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 233
  (Polychromatic418967fa.accept_19_14_2_5_1_9949 71 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 116 233 (accept_3_2 70 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 233 (accept_3_2 67 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 233 (Polychromatic418967fa.accept_17_15_14_12_1_1973 66 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 233 (accept_3_2 64 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 233 (accept_3_2 61 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 233 (Polychromatic418967fa.accept_16_12_4_9_1_4633 60 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 233
  (Polychromatic418967fa.accept_10_9_6_3_1_545 59 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 233 (accept_3_2 58 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 233 (Polychromatic418967fa.accept_16_8_4_9_1_4666 56 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 233 (accept_3_2 55 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 233 (accept_3_2 52 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 50 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 233 (accept_3_2 49 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 233 (accept_3_2 46 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 233 (accept_3_2 43 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 42 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 233 (accept_3_2 40 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 233 (accept_3_2 37 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 233 (Polychromatic418967fa.accept_19_17_2_5_1_7085 36 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 233 (accept_3_2 34 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 233 (Polychromatic418967fa.accept_17_15_14_12_1_1973 32 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 233 (accept_3_2 31 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 116
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 233 (accept_3_2 28 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 233 (accept_3_2 25 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 233 (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 233
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 233 (accept_3_2 22 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 233 (accept_3_2 19 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 233 (accept_3_2 16 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 233 (accept_3_2 13 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 233
  (Polychromatic418967fa.accept_16_11_4_9_1_851 11 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 233 (accept_3_2 10 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 233 (accept_3_2 7 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 233 (accept_3_2 4 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 233 (accept_3_2 1 116 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 233 (allA_of_3_0 115 115 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 233
  (allA_succ_of_accept 113 114 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 113 114 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 233 (accept_3_2 112 114 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 110 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 233 (accept_3_2 109 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 108 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 233 (accept_3_2 106 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 105 114
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 104 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 233 (accept_3_2 103 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 114 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 101 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 233 (accept_3_2 100 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 233
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 98 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 114 233 (accept_3_2 97 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 114 233 (Polychromatic418967fa.accept_21_12_9_2_1_7941 96 114 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 233 (accept_3_2 94 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308
  93 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 233 (accept_3_2 91 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 233 (Polychromatic418967fa.accept_21_6_9_2_1_9554 90 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 89 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 233 (accept_3_2 88 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 233 (accept_3_2 85 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 233 (accept_3_2 82 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 233 (Polychromatic418967fa.accept_14_11_2_9_1_5873 81 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 233
  (Polychromatic418967fa.accept_13_2_10_12_1_757 80 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 233 (accept_3_2 79 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 114 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 78 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 233 (accept_3_2 76 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 233 (accept_3_2 73 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 114 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 233 (accept_3_2 70 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 69 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 233 (accept_3_2 67 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 114 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 233 (accept_3_2 64 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 233
  (Polychromatic418967fa.accept_15_2_9_8_1_736 62 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 233 (accept_3_2 61 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 233 (accept_3_2 58 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 233 (accept_3_2 55 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 54 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 233 (accept_3_2 52 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 233 (accept_3_2 49 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 233 (accept_3_2 46 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 233
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 44 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 233 (accept_3_2 43 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 233 (accept_3_2 40 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 233 (accept_3_2 37 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 233 (Polychromatic418967fa.accept_21_15_9_2_1_7973 36 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 233 (accept_3_2 34 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 233 (accept_3_2 31 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 233 (accept_3_2 28 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 233
  (Polychromatic418967fa.accept_28_26_2_9_1_13920 26 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 114 233 (accept_3_2 25 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 114 233 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 233 (accept_3_2 22
  114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 233
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 114 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 233 (accept_3_2 19 114 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 233 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 233
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 233 (accept_3_2 16 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 233 (accept_3_2 13 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 233 (accept_3_2 10 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 233 (accept_3_2 7 114 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 114 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 233 (accept_3_2 4 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 233 (accept_3_2 1 114 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 233 (allA_succ_of_accept 112 113 233 (accept_3_2 112 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 113 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 113
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 233 (accept_3_2 109 113
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 108 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 107 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 233 (accept_3_2 106 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 104 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 233 (accept_3_2 103 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 233 (accept_3_2 100 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 99 113
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 233
  (Polychromatic418967fa.accept_16_2_1_9_1_2577 98 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 233 (accept_3_2 97 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 233 (Polychromatic418967fa.accept_25_20_13_8_1_13919 95 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 233 (accept_3_2 94 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 233 (accept_3_2 91 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 233 (Polychromatic418967fa.accept_11_1_3_2_1_1090 89 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 233 (accept_3_2 88 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 233
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 86 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 233 (accept_3_2 85 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 233 (accept_3_2 82 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 233 (accept_3_2 79 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 233 (Polychromatic418967fa.accept_16_13_1_9_1_2597 77 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 233 (accept_3_2 76 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 233 (accept_3_2 73 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 233 (Polychromatic418967fa.accept_16_8_1_9_1_847 72 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 233 (Polychromatic418967fa.accept_25_21_13_8_1_13918 71 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 233 (accept_3_2 70 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 233
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 68 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 233 (accept_3_2 67 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 233 (accept_3_2 64 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 233 (Polychromatic418967fa.accept_19_6_18_5_1_5630 63 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 233 (accept_3_2 61 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 233 (accept_3_2 58 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 233 (accept_3_2 55 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 233 (Polychromatic418967fa.accept_22_10_3_13_1_10972 54 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 233 (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 233 (accept_3_2 52 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 233
  (Polychromatic418967fa.accept_14_8_1_9_1_2085 50 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 233 (accept_3_2 49 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 233 (accept_3_2 46 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 233
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 233 (accept_3_2 43 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 233 (accept_3_2 40 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 233 (accept_3_2 37 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 233 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 233 (Polychromatic418967fa.accept_21_14_8_2_1_11088 35 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 233 (accept_3_2 34 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 233
  (Polychromatic418967fa.accept_19_13_18_5_1_8619 32 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 233 (accept_3_2 31 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 233 (accept_3_2 28 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230
  27 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 233
  (Polychromatic418967fa.accept_16_10_1_9_1_4622 26 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 233 (accept_3_2 25 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 233 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 233 (accept_3_2 22 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 233 (accept_3_2 19 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 233 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 233 (accept_3_2 16 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 233
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 233 (accept_3_2 13 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 233 (accept_3_2 10 113 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 233 (Polychromatic418967fa.accept_19_9_18_5_1_7101
  9 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 233
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 233 (accept_3_2 7 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 233 (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 233 (accept_3_2 4 113 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 233 (accept_3_2 1 113 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 233 (allA_of_3_0 112 112 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 233
  (allA_succ_of_accept 110 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 110 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 233 (accept_3_2 109 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 233
  (Polychromatic418967fa.accept_15_2_6_8_1_754 107 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 233 (accept_3_2 106 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 233 (accept_3_2 103 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 233 (accept_3_2 100 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 233 (accept_3_2 97 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 233 (accept_3_2 94 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 233 (accept_3_2 91 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 233
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 89 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 111 233 (accept_3_2 88 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 233 (accept_3_2 85 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 233
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 233 (accept_3_2 82 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80
  111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 233 (accept_3_2 79
  111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 233 (accept_3_2 76 111 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 75 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 233 (accept_3_2 73 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 111 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 233 (accept_3_2 70 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 233 (accept_3_2 67 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 111 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 233 (accept_3_2 64 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 233 (accept_3_2 61 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 233 (accept_3_2 58 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 233 (accept_3_2 55 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 233 (accept_3_2 52 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 233 (accept_3_2 49 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 233 (accept_3_2 46 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 233 (accept_3_2 43 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 233 (accept_3_2 40 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 233 (accept_3_2 37 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 233 (Polychromatic418967fa.accept_20_15_11_13_1_11192 35 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 233 (accept_3_2 34 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 233 (accept_3_2 31 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 233 (accept_3_2 28 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 233 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 233 (accept_3_2 25 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 233 (accept_3_2 22 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 111 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 233 (accept_3_2 19 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 233 (accept_3_2 16 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 233 (accept_3_2 13 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 233 (accept_3_2 10 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 233 (accept_3_2 7 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 233 (accept_3_2 4 111 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 233 (accept_3_2 1 111 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 233 (allA_succ_of_accept 109 110 233 (accept_3_2 109 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 107 110
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 233 (accept_3_2 106 110
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 233 (accept_3_2 103 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 101 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 233 (accept_3_2 100 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 98 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 233 (accept_3_2 97 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 110 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 95 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 110 233 (accept_3_2 94 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 110 233 (Polychromatic418967fa.accept_12_8_2_5_1_844 92 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 233 (accept_3_2 91 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 233 (Polychromatic418967fa.accept_17_5_8_12_1_6609 90 110
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 89 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 233 (accept_3_2 88 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 233 (accept_3_2 85 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 233 (accept_3_2 82 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 233 (accept_3_2 79 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 233 (accept_3_2 76 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 233 (accept_3_2 73 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 110 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 233 (accept_3_2 70 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 233 (accept_3_2 67 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 233
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 65 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 110 233 (accept_3_2 64 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 62 110
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 233 (accept_3_2 61 110
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 233 (accept_3_2 58 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 233 (accept_3_2 55
  110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 233
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 110 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 233 (accept_3_2 52 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109
  50 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 233 (accept_3_2 49
  110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 233 (accept_3_2 46 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 233 (accept_3_2 43
  110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 233 (accept_3_2 40 110 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 233 (accept_3_2 37
  110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 233
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 233 (accept_3_2 34 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 233 (accept_3_2 31 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 233 (accept_3_2 28 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 233 (accept_3_2 25 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 233 (accept_3_2 22 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 233 (accept_3_2 19 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 233 (accept_3_2 16 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 233 (accept_3_2 13 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 233 (accept_3_2 10 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 233 (accept_3_2 7 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 233 (accept_3_2 4 110 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 233
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 233 (accept_3_2 1 110 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 233 (allA_of_3_0 109 109 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 233
  (allA_succ_of_accept 107 108 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 107 108 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 233 (accept_3_2 106 108 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 105 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 104 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 233 (accept_3_2 103 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 102 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 101 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 233 (accept_3_2 100 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 233
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 98 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 233 (accept_3_2 97 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 95 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 233 (accept_3_2 94 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 93 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 92 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 233 (accept_3_2 91 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 233 (accept_3_2 88 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 87 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 86 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 233 (accept_3_2 85 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 108 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 84 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 233 (accept_3_2 82 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 233
  (Polychromatic418967fa.accept_13_2_4_12_1_745 80 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 233 (accept_3_2 79 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 233 (accept_3_2 76 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 233
  (Polychromatic418967fa.accept_20_14_8_13_1_8293 74 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 108 233 (accept_3_2 73 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 108 233 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 108 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 233 (accept_3_2 70 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461
  69 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 233 (accept_3_2 67 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 65 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 233 (accept_3_2 64 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 108
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 233 (accept_3_2 61 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 59 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 233 (accept_3_2 58 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 233 (accept_3_2 55 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 233 (accept_3_2 52 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 233 (accept_3_2 49 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 233 (accept_3_2 46 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 233
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 233 (accept_3_2 43 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 233 (accept_3_2 40 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 233
  (Polychromatic418967fa.accept_20_18_8_13_1_6761 38 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 233 (accept_3_2 37 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 108
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 233 (accept_3_2 34 108
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 233 (Polychromatic418967fa.accept_23_9_16_3_1_12408 32 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 233 (accept_3_2 31 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 233 (Polychromatic418967fa.accept_19_11_13_5_1_5714 30 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 233 (accept_3_2 28 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 233 (accept_3_2 25 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 233
  (Polychromatic418967fa.accept_20_3_8_13_1_3832 23 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 233 (accept_3_2 22 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 233 (accept_3_2 19 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 233
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 233 (accept_3_2 16 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 233 (Polychromatic418967fa.accept_19_14_13_5_1_9905 14 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 233 (accept_3_2 13 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 233
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 233 (accept_3_2 10 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 233 (accept_3_2 7 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 233 (accept_3_2 4 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 108 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 233 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 233 (accept_3_2 1 108 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 233 (allA_succ_of_accept 106 107 233 (accept_3_2 106 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 107 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 104 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 233 (accept_3_2 103 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 233 (Polychromatic418967fa.accept_16_5_11_9_1_861 101 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 233 (accept_3_2 100 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 99 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 233 (accept_3_2 97 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 95 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 233 (accept_3_2 94 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 93 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 233
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 92 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 233 (accept_3_2 91 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 233 (Polychromatic418967fa.accept_19_13_12_5_1_9943 89 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 233 (accept_3_2 88 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 87 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 233 (accept_3_2 85 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 233 (Polychromatic418967fa.accept_19_7_12_5_1_7123 83 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 233 (accept_3_2 82 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 81 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 233
  (Polychromatic418967fa.accept_13_2_3_12_1_735 80 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 233 (accept_3_2 79 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 233 (Polychromatic418967fa.accept_17_9_5_12_1_6606 77 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 233 (accept_3_2 76 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 233 (accept_3_2 73 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 233 (Polychromatic418967fa.accept_19_15_12_5_1_8544 72 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 233 (accept_3_2 70 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 69 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 233
  (Polychromatic418967fa.accept_16_4_11_9_1_1631 68 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 233 (accept_3_2 67 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 65 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 233 (accept_3_2 64 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 233 (Polychromatic418967fa.accept_27_9_26_17_1_980 63 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 233 (accept_3_2 61 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 233 (Polychromatic418967fa.accept_17_8_5_12_1_7925 59 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 233 (accept_3_2 58 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 233 (Polychromatic418967fa.accept_23_11_15_3_1_13917 57
  107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 233
  (Polychromatic418967fa.accept_10_6_7_3_1_547 56 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 233 (accept_3_2 55 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 233 (Polychromatic418967fa.accept_16_5_11_9_1_861 53 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 233 (accept_3_2 52 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 51 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 233 (accept_3_2 49 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 233 (Polychromatic418967fa.accept_19_9_12_5_1_5695 47 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 233 (accept_3_2 46 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 233
  (Polychromatic418967fa.accept_10_4_7_3_1_54 44 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 233 (accept_3_2 43 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 233 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 233 (accept_3_2 40 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 39 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 233 (accept_3_2 37 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 233 (accept_3_2 34 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 233 (Polychromatic418967fa.accept_22_11_19_13_1_9237 33
  107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 233
  (Polychromatic418967fa.accept_19_13_12_5_1_9943 32 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 107 233 (accept_3_2 31 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 233 (Polychromatic418967fa.accept_22_7_19_13_1_10815 29
  107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 233 (accept_3_2 28
  107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 233
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 233 (accept_3_2 25 107 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 107 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 233
  (Polychromatic418967fa.accept_19_4_12_5_1_8615 23 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 233 (accept_3_2 22 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 233 (Polychromatic418967fa.accept_16_4_11_9_1_1631 20 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 233 (accept_3_2 19 107 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 233
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 233 (accept_3_2 16 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 233 (accept_3_2 13 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 233 (Polychromatic418967fa.accept_23_12_15_3_1_13916 12 107 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 233
  (Polychromatic418967fa.accept_19_11_12_5_1_7124 11 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 107 233 (accept_3_2 10 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 107 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 107 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 233 (Polychromatic418967fa.accept_17_8_5_12_1_7925 8 107
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 233 (accept_3_2 7 107 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 233 (accept_3_2 4 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 233 (Polychromatic418967fa.accept_24_3_11_17_1_10650 3 107 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 233 (accept_3_2 1 107 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 233 (allA_of_3_0 106 106 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 233
  (allA_succ_of_accept 104 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 233 (accept_3_2 103 105 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 233 (accept_3_2 100 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 99 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 233 (accept_3_2 97 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 96 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 233 (accept_3_2 94 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 233 (accept_3_2 91 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 233 (Polychromatic418967fa.accept_19_14_10_5_1_3073 90 105 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 233
  (Polychromatic418967fa.accept_13_11_1_12_1_742 89 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 233 (accept_3_2 88 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 233 (accept_3_2 85 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 233 (accept_3_2 82 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 233 (accept_3_2 79 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 78 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 233 (accept_3_2 76 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 233 (accept_3_2 73 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 233
  (Polychromatic418967fa.accept_19_14_10_5_1_3073 71 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 105 233 (accept_3_2 70 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 105 233 (Polychromatic418967fa.accept_26_17_1_25_1_13915 69 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 233 (accept_3_2 67
  105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 233
  (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 105 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 233 (accept_3_2 64 105 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 233 (accept_3_2 61 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 105 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 105 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 233 (accept_3_2 58 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 233 (accept_3_2 55 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 233 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 233 (Polychromatic418967fa.accept_19_15_10_5_1_5637 53 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 233 (accept_3_2 52 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 233 (accept_3_2 49 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 233 (accept_3_2 46 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 233 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 105 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 233 (accept_3_2 43 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 233 (accept_3_2 40 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 233 (accept_3_2 37 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 233 (Polychromatic418967fa.accept_25_11_5_8_1_13914 36 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 233 (Polychromatic418967fa.accept_19_16_10_5_1_7106 35 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 233 (accept_3_2 34 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 233 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 105
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 233 (accept_3_2 31 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 233 (accept_3_2 28 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 233 (accept_3_2 25 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 233 (accept_3_2 22 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 233 (accept_3_2 19 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 233 (accept_3_2 16 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 105 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 233 (accept_3_2 13 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 233 (accept_3_2 10 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 233 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 233 (accept_3_2 7 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 233 (Polychromatic418967fa.accept_18_6_15_17_1_7363 6 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 233 (accept_3_2 4 105 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 233 (accept_3_2 1 105 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 233 (allA_succ_of_accept 103 104 233 (accept_3_2 103 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 104 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 104
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 233 (accept_3_2 100 104
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 104 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 233 (accept_3_2 97 104 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451
  95 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 104 233 (accept_3_2 94
  104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 104 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 104 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 104 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 233 (accept_3_2 91 104 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 104 233 (Polychromatic418967fa.accept_19_14_9_5_1_9941 90 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 233
  (Polychromatic418967fa.accept_10_9_4_3_1_539 89 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 233 (accept_3_2 88 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 86 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 233 (accept_3_2 85 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 233 (accept_3_2 82 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 233 (accept_3_2 79 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 233
  (Polychromatic418967fa.accept_10_7_4_3_1_560 77 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 233 (accept_3_2 76 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 233 (accept_3_2 73 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 233 (Polychromatic418967fa.accept_17_4_2_12_1_6554 72 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 233 (accept_3_2 70 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 233 (Polychromatic418967fa.accept_16_4_8_9_1_4639 68 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 233 (accept_3_2 67 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 233 (accept_3_2 64 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 233 (accept_3_2 61 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 233 (accept_3_2 58 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 233 (accept_3_2 55 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 54 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 233 (accept_3_2 52 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 233 (accept_3_2 49 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 233 (accept_3_2 46 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 233 (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 233 (accept_3_2 43 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 233
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 233 (accept_3_2 40 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 233 (accept_3_2 37 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 233 (accept_3_2 34 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 233 (accept_3_2 31 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 233 (accept_3_2 28 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 233 (accept_3_2 25 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 233
  (Polychromatic418967fa.accept_16_7_8_9_1_9427 23 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 233 (accept_3_2 22 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 233 (accept_3_2 19 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 233 (accept_3_2 16 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 233 (accept_3_2 13 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 233 (accept_3_2 10 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 233 (accept_3_2 7 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 233 (accept_3_2 4 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 233 (accept_3_2 1 104 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 233 (allA_of_3_0 103 103 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 233 (allA_succ_of_accept 101
  102 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 233 (accept_3_2 100 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 102 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 98 102
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 233 (accept_3_2 97 102
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 96 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 102 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 102 233 (accept_3_2 94 102 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 102 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 93 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 102 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 102 233 (accept_3_2 91 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 102 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 102 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 233 (accept_3_2 88 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 233 (accept_3_2 85 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 102 233 (Polychromatic418967fa.accept_22_18_14_13_1_12531 84 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 233 (accept_3_2 82 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 102
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 233
  (Polychromatic418967fa.accept_15_5_12_8_1_3168 80 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 233 (accept_3_2 79 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 233 (accept_3_2 76 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 233 (accept_3_2 73 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 233 (accept_3_2 70 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 233 (accept_3_2 67 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 66 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 233 (accept_3_2 64 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 233 (accept_3_2 61 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 102 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 233 (accept_3_2 58 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 233 (Polychromatic418967fa.accept_21_15_18_2_1_6376 57 102 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 233 (accept_3_2 55 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 233 (accept_3_2 52 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 233 (accept_3_2 49 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 233 (accept_3_2 46 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 233
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 233 (accept_3_2 43 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 233 (accept_3_2 40 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 233 (accept_3_2 37 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 233 (accept_3_2 34 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 233 (accept_3_2 31 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 233 (accept_3_2 28 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 233 (accept_3_2 25 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 233 (accept_3_2 22 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 233 (accept_3_2 19 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 233 (accept_3_2 16 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 233 (accept_3_2 13 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 233 (accept_3_2 10 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 233 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 233
  (Polychromatic418967fa.accept_24_8_6_17_1_5282 8 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 233 (accept_3_2 7 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 233 (accept_3_2 4 102 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 233 (accept_3_2 1 102 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 233 (allA_succ_of_accept 100 101 233 (accept_3_2 100 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 98 101
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 233 (accept_3_2 97 101
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 96 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 233 (accept_3_2 94 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 92
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 233 (accept_3_2 91
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 90 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 233 (accept_3_2 88 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 101 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109
  86 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 233 (accept_3_2 85
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 84 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 233 (accept_3_2 82 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 101 233 (Polychromatic418967fa.accept_16_1_5_9_1_1649 81 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 233
  (Polychromatic418967fa.accept_13_2_10_12_1_757 80 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 233 (accept_3_2 79 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 233 (accept_3_2 76 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 233
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 74 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 101 233 (accept_3_2 73 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 101 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 233 (accept_3_2 70 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461
  69 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 233 (accept_3_2 67 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 233 (accept_3_2 64 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 233 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 233 (accept_3_2 61 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 233 (accept_3_2 58 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 233
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 101 233 (accept_3_2 55 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 233 (Polychromatic418967fa.accept_19_15_6_5_1_4356 53 101
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 233 (accept_3_2 52 101
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 233 (accept_3_2 49 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 233 (accept_3_2 46
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 233
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 233 (accept_3_2 43 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 233 (accept_3_2 40 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 233 (accept_3_2 37 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 233
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 101 233 (accept_3_2 34 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 233 (accept_3_2 31 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108
  30 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 233 (accept_3_2 28 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 233 (accept_3_2 25 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 233 (accept_3_2 22 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 233 (accept_3_2 19 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 233
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 233 (accept_3_2 16 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 233 (accept_3_2 13 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 233
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 233 (accept_3_2 10 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 101 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 233 (accept_3_2 7 101 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 233 (accept_3_2 4 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 233 (accept_3_2 1 101 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 233 (allA_of_3_0 100 100 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 233 (allA_succ_of_accept 98 99
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 233 (accept_3_2 97 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 96 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 233 (Polychromatic418967fa.accept_13_4_8_12_1_3526 95 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 233 (accept_3_2 94 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 233 (accept_3_2 91 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 233 (Polychromatic418967fa.accept_15_14_9_8_1_3165 89 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 233 (accept_3_2 88 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 233 (accept_3_2 85 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 233 (accept_3_2 82 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 233 (accept_3_2 79 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 233 (Polychromatic418967fa.accept_15_2_9_8_1_736 77 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 233 (accept_3_2 76 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 233 (Polychromatic418967fa.accept_13_10_8_12_1_2032 75 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 233 (accept_3_2 73 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 233 (Polychromatic418967fa.accept_16_7_3_9_1_2557 71 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 233 (accept_3_2 70 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 233 (accept_3_2 67 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 233 (Polychromatic418967fa.accept_19_8_4_5_1_8569 65 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 233 (accept_3_2 64 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 233 (accept_3_2 61 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 233 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 233 (accept_3_2 58 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 233 (accept_3_2 55 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 233 (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 233 (accept_3_2 52 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 233 (Polychromatic418967fa.accept_18_15_9_17_1_6043 51 99
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 233 (accept_3_2 49 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 233 (Polychromatic418967fa.accept_15_2_9_8_1_736 47 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 233 (accept_3_2 46 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 233 (accept_3_2 43 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 233 (accept_3_2 40 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 233 (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 233 (accept_3_2 37 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 233 (accept_3_2 34 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 233 (accept_3_2 31 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 233 (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 233 (accept_3_2 28 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 233 (accept_3_2 25 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 233 (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 233 (accept_3_2 22 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 233 (accept_3_2 19 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 233 (accept_3_2 16 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 233 (Polychromatic418967fa.accept_17_15_14_12_1_1973 15 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 233 (accept_3_2 13 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 233 (Polychromatic418967fa.accept_16_12_3_9_1_5886 12 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 233 (Polychromatic418967fa.accept_17_11_14_12_1_2995 11 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 233 (accept_3_2 10 99 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 233 (accept_3_2 7 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 99 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 233 (accept_3_2 4 99 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 233 (accept_3_2 1 99 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  233 (allA_succ_of_accept 97 98 233 (accept_3_2 97 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 233 (accept_3_2 94 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 92 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 233 (accept_3_2 91 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 233 (Polychromatic418967fa.accept_19_14_3_5_1_11347 90 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 89 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 233 (accept_3_2 88 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 86 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 233 (accept_3_2 85 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 233 (accept_3_2 82 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 233 (accept_3_2 79 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 233 (Polychromatic418967fa.accept_18_5_8_17_1_3478 77 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 233 (accept_3_2 76 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 233
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 74 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 233 (accept_3_2 73 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 233 (Polychromatic418967fa.accept_21_9_14_2_1_6370 72 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 233 (accept_3_2 70 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 233 (accept_3_2 67 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 65 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 233 (accept_3_2 64 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 233
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 233 (accept_3_2 61 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 233 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 233 (accept_3_2 58 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 233 (accept_3_2 55 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 233 (Polychromatic418967fa.accept_16_6_2_9_1_5897 54 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 233 (Polychromatic418967fa.accept_21_11_14_2_1_6371 53 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 233 (accept_3_2 52 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 233
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 233 (accept_3_2 49 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 233 (Polychromatic418967fa.accept_19_10_3_5_1_11346 48 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 233 (accept_3_2 46 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 233 (accept_3_2 43 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 233 (Polychromatic418967fa.accept_20_2_18_13_1_3843 42 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 41 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 233 (accept_3_2 40 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 233
  (Polychromatic418967fa.accept_16_6_2_9_1_5897 38 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 233 (accept_3_2 37 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 233 (accept_3_2 34 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 233 (accept_3_2 31 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 233 (Polychromatic418967fa.accept_19_10_3_5_1_11346 29 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 233 (accept_3_2 28 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 233 (accept_3_2 25 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 233 (accept_3_2 22 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 233 (accept_3_2 19 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 233 (accept_3_2 16 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 233
  (Polychromatic418967fa.accept_19_14_3_5_1_11347 14 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 233 (accept_3_2 13 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 233 (accept_3_2 10 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 233 (accept_3_2 7 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  233 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 98 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 233 (accept_3_2 4 98 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 233 (Polychromatic418967fa.accept_18_2_8_17_1_4754
  2 98 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 233 (accept_3_2 1 98
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  233 (allA_of_3_0 97 97 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 233 (allA_succ_of_accept 95 96 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 233 (accept_3_2 94 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 233 (accept_3_2 91 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 233 (Polychromatic418967fa.accept_21_6_12_2_1_4801 90 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 233
  (Polychromatic418967fa.accept_10_9_6_3_1_545 89 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 233 (accept_3_2 88 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 233 (accept_3_2 85 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 233 (accept_3_2 82 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 233 (accept_3_2 79 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 233 (accept_3_2 76 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 233 (accept_3_2 73 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 233
  (Polychromatic418967fa.accept_11_5_8_2_1_588 71 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 233 (accept_3_2 70 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 233 (accept_3_2 67 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 233 (accept_3_2 64 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 233 (Polychromatic418967fa.accept_14_7_12_9_1_2926 63 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 233 (Polychromatic418967fa.accept_15_2_6_8_1_754 62 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 233 (accept_3_2 61 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 233 (accept_3_2 58 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 233 (accept_3_2 55 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 233 (accept_3_2 52 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 233 (Polychromatic418967fa.accept_18_15_6_17_1_2386 51 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 233 (accept_3_2 49 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 233 (accept_3_2 46 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 233 (accept_3_2 43 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 233 (Polychromatic418967fa.accept_19_4_1_5_1_9933 42 96 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 233 (accept_3_2 40 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 233 (accept_3_2 37 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 233 (Polychromatic418967fa.accept_23_13_4_3_1_13913 36 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 233
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 233 (accept_3_2 34 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 233 (accept_3_2 31 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 233 (accept_3_2 28 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 233 (Polychromatic418967fa.accept_25_1_21_8_1_13912 26 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 233 (accept_3_2 25 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 233 (accept_3_2 22 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 233 (accept_3_2 19 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 233 (accept_3_2 16 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 233 (accept_3_2 13 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 233 (accept_3_2 10 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 233 (accept_3_2 7 96 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 233 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 96 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 233 (accept_3_2 4 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 96 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 233 (accept_3_2 1 96 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 233
  (allA_succ_of_accept 94 95 233 (accept_3_2 94 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 233 (accept_3_2 91 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 233 (accept_3_2 88 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 233 (accept_3_2 85 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 233 (accept_3_2 82 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 81 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 233 (Polychromatic418967fa.accept_13_2_4_12_1_745 80 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 233 (accept_3_2 79 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 233 (accept_3_2 76 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 233 (accept_3_2 73 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 71 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 233 (accept_3_2 70 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 233 (accept_3_2 67 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 233 (accept_3_2 64 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 233 (accept_3_2 61 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 233
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 233 (accept_3_2 58 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 233 (accept_3_2 55 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 233
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 233 (accept_3_2 52 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 233 (accept_3_2 49 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 233 (accept_3_2 46 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 233 (Polychromatic418967fa.accept_20_5_15_13_1_5235 45 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 233 (accept_3_2 43 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 233 (accept_3_2 40 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 233 (accept_3_2 37 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 233 (Polychromatic418967fa.accept_17_2_10_12_1_7915 36 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 233
  (Polychromatic418967fa.accept_21_14_11_2_1_13897 35 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 95 233 (accept_3_2 34 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 95 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 233 (accept_3_2 31 95 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 233 (accept_3_2 28 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 233 (accept_3_2 25 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 233
  (Polychromatic418967fa.accept_17_6_10_12_1_4129 23 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 233 (accept_3_2 22 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 233 (accept_3_2 19 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 233 (accept_3_2 16 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 233 (accept_3_2 13 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 233 (accept_3_2 10 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 233 (accept_3_2 7 95 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 233 (accept_3_2 4 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 233 (accept_3_2 1 95 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 233
  (allA_of_3_0 94 94 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 233 (allA_succ_of_accept 92 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 233 (accept_3_2 91 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 233 (Polychromatic418967fa.accept_17_5_8_12_1_6609 90 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 233 (Polychromatic418967fa.accept_17_4_8_12_1_9165 89 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 233 (accept_3_2 88 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 93 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 233 (accept_3_2 85 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 233 (accept_3_2 82 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 233 (Polychromatic418967fa.accept_13_3_2_12_1_2797 81 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 233 (accept_3_2 79 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 233 (accept_3_2 76 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 233 (accept_3_2 73 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 233 (accept_3_2 70 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 233 (accept_3_2 67 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 233 (accept_3_2 64 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 233 (accept_3_2 61 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 233 (accept_3_2 58 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 57 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 233 (accept_3_2 55 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 233 (accept_3_2 52 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 233 (accept_3_2 49 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 233 (Polychromatic418967fa.accept_21_6_9_2_1_9554 48 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 233 (accept_3_2 46 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 233 (accept_3_2 43 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 233 (accept_3_2 40 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 233 (accept_3_2 37 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 233 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 233 (accept_3_2 34 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 233 (accept_3_2 31 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 233 (accept_3_2 28 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 233 (accept_3_2 25 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 233 (accept_3_2 22 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 233 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 233 (accept_3_2 19 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 233 (accept_3_2 16 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 233 (accept_3_2 13 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 233 (accept_3_2 10 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 93 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 233 (accept_3_2 7 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 233 (accept_3_2 4 93 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 233 (accept_3_2 1 93 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 233
  (allA_succ_of_accept 91 92 233 (accept_3_2 91 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 89 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 233 (accept_3_2 88 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 233 (accept_3_2 85 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 233 (accept_3_2 82 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 233 (accept_3_2 79 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 233 (accept_3_2 76 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 233 (accept_3_2 73 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 233 (accept_3_2 70 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 233 (accept_3_2 67 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 65 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 233 (accept_3_2 64 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 233 (accept_3_2 61 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 233 (accept_3_2 58 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 233
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 233 (accept_3_2 55 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 233 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 233 (accept_3_2 52 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 233 (accept_3_2 49 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 233 (accept_3_2 46 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 233
  (Polychromatic418967fa.accept_13_5_1_12_1_740 44 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 233 (accept_3_2 43 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 233 (accept_3_2 40 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 233 (accept_3_2 37 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 233 (accept_3_2 34 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 233 (accept_3_2 31 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 233 (accept_3_2 28 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 233 (accept_3_2 25 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 233 (accept_3_2 22 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 233 (accept_3_2 19 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 233 (accept_3_2 16 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 233 (accept_3_2 13 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 233 (accept_3_2 10 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 233
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 233 (accept_3_2 7 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 92 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 233 (accept_3_2 4 92 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 233 (accept_3_2 1 92 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 233
  (allA_of_3_0 91 91 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 233 (allA_succ_of_accept 89 90 233
  (Polychromatic418967fa.accept_19_13_14_5_1_8545 89 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 233 (accept_3_2 88 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 233 (Polychromatic418967fa.accept_19_10_14_5_1_3079 86 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 233 (accept_3_2 85 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 233 (Polychromatic418967fa.accept_19_8_14_5_1_9919 84 90
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 233 (accept_3_2 82 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 233 (accept_3_2 79 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 233
  (Polychromatic418967fa.accept_17_9_5_12_1_6606 77 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 233 (accept_3_2 76 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 233 (accept_3_2 73 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 233 (Polychromatic418967fa.accept_20_12_10_13_1_9747 72 90 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 233 (accept_3_2 70 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 233 (Polychromatic418967fa.accept_20_9_10_13_1_3835 69 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 233 (Polychromatic418967fa.accept_19_11_14_5_1_5629 68 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 233 (accept_3_2 67 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 90 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 233
  (Polychromatic418967fa.accept_16_1_10_9_1_4645 65 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 233 (accept_3_2 64 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 233 (Polychromatic418967fa.accept_20_2_10_13_1_6766 62 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 233 (accept_3_2 61 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 90 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 233 (accept_3_2 58 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 233 (Polychromatic418967fa.accept_21_14_6_2_1_4793 56 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 233 (accept_3_2 55 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 233 (Polychromatic418967fa.accept_19_16_14_5_1_9920 54 90
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 233 (accept_3_2 52 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 233 (accept_3_2 49 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 233 (Polychromatic418967fa.accept_19_10_14_5_1_3079 48 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 233 (accept_3_2 46 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 233 (Polychromatic418967fa.accept_17_10_5_12_1_4101 44 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 233 (accept_3_2 43 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 233 (Polychromatic418967fa.accept_17_8_5_12_1_7925 42 90
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 233
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 233 (accept_3_2 40 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 233 (accept_3_2 37 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 233 (accept_3_2 34 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 233 (Polychromatic418967fa.accept_16_1_10_9_1_4645 33 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 233 (accept_3_2 31 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 233 (Polychromatic418967fa.accept_19_11_14_5_1_5629 30 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 233 (accept_3_2 28 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 233 (Polychromatic418967fa.accept_17_9_5_12_1_6606 26 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 233 (accept_3_2 25 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 233 (accept_3_2 22 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 233 (Polychromatic418967fa.accept_19_2_14_5_1_5715 21 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 233 (Polychromatic418967fa.accept_21_20_6_2_1_11048 20 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 233 (accept_3_2 19 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 233 (accept_3_2 16 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 233 (Polychromatic418967fa.accept_21_14_6_2_1_4793 14 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 233 (accept_3_2 13 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 233 (Polychromatic418967fa.accept_20_12_10_13_1_9747 12 90
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 233 (accept_3_2 10 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 233 (Polychromatic418967fa.accept_17_9_5_12_1_6606 9 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 233 (accept_3_2 7 90 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 233 (Polychromatic418967fa.accept_19_6_14_5_1_4339 6 90 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 233
  (Polychromatic418967fa.accept_20_5_10_13_1_6754 5 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 233 (accept_3_2 4 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 233 (Polychromatic418967fa.accept_19_2_14_5_1_5715 2 90 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 233 (accept_3_2 1 90 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 233 (allA_succ_of_accept 88 89 233 (accept_3_2 88 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 89 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 86 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 233 (accept_3_2 85 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  84 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 233
  (Polychromatic418967fa.accept_19_7_13_5_1_7125 83 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 233 (accept_3_2 82 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 233 (accept_3_2 79 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 233 (Polychromatic418967fa.accept_22_12_1_13_1_1623 78 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 233
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 77 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 233 (accept_3_2 76 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 233 (accept_3_2 73 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 233
  (Polychromatic418967fa.accept_19_14_13_5_1_9905 71 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 233 (accept_3_2 70 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 233 (Polychromatic418967fa.accept_19_11_13_5_1_5714 68 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 233 (accept_3_2 67 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 233
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 233 (accept_3_2 64 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 233 (Polychromatic418967fa.accept_14_7_5_9_1_2911 63 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 62 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 233 (accept_3_2 61 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 233 (accept_3_2 58 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 233 (Polychromatic418967fa.accept_26_5_11_25_1_13911 57 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 233 (accept_3_2 55 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 233 (accept_3_2 52 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 233 (Polychromatic418967fa.accept_15_6_14_8_1_245 51 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 50 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 233 (accept_3_2 49 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 233 (Polychromatic418967fa.accept_19_10_13_5_1_3091 48 89
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 233
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 233 (accept_3_2 46 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 233 (accept_3_2 43 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 233 (Polychromatic418967fa.accept_17_8_4_12_1_1994 42 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 233
  (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 233 (accept_3_2 40 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 233 (accept_3_2 37 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 233
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 233 (accept_3_2 34 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 233 (accept_3_2 31 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 233
  (Polychromatic418967fa.accept_19_10_13_5_1_3091 29 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 233 (accept_3_2 28 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 233 (accept_3_2 25 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 233
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 89 233 (accept_3_2 22 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 89 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 89 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 89
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 233 (accept_3_2 19 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18
  89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 233 (accept_3_2 16 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 233 (Polychromatic418967fa.accept_23_15_20_3_1_13910 15 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 233 (accept_3_2 13 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 233 (Polychromatic418967fa.accept_19_12_13_5_1_11331 12 89 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 233 (accept_3_2 10 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 233 (Polychromatic418967fa.accept_17_8_4_12_1_1994 8 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 233 (accept_3_2 7 89 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 89 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 233 (accept_3_2 4 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 233 (Polychromatic418967fa.accept_17_2_4_12_1_6587 2 89 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 233 (accept_3_2 1 89 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 233 (allA_of_3_0 88 88 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 233
  (allA_succ_of_accept 86 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 233 (accept_3_2 85 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 83
  87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 233 (accept_3_2 82 87
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 233
  (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 233 (accept_3_2 79 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 77
  87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 233 (accept_3_2 76 87
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 233 (accept_3_2 73 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 233 (Polychromatic418967fa.accept_16_8_7_9_1_7052 72 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71
  87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 233 (accept_3_2 70 87
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 233 (accept_3_2 67 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65
  87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 233 (accept_3_2 64 87
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 233
  (Polychromatic418967fa.accept_15_3_12_8_1_738 63 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 233 (accept_3_2 61 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 233 (accept_3_2 58 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 233 (accept_3_2 55 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 233
  (Polychromatic418967fa.accept_19_15_11_5_1_5713 53 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 233 (accept_3_2 52 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 233 (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 233 (accept_3_2 49 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 233 (accept_3_2 46 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 233 (accept_3_2 43 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 233 (accept_3_2 40 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 233 (accept_3_2 37 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 233 (accept_3_2 34 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 233 (accept_3_2 31 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 233 (accept_3_2 28 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 233 (accept_3_2 25 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 233 (accept_3_2 22 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 233 (accept_3_2 19 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 233
  (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 233 (accept_3_2 16 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 233 (accept_3_2 13 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 233 (accept_3_2 10 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 233 (accept_3_2 7 87 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 233 (accept_3_2 4 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 233 (accept_3_2 1 87 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 233 (allA_succ_of_accept 85 86 233 (accept_3_2 85 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 86 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 233 (accept_3_2 82 86 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 233 (accept_3_2 79 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 77 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 233 (accept_3_2 76 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 233 (accept_3_2 73 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 233 (accept_3_2 70 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 233 (accept_3_2 67 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 233 (accept_3_2 64 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 233
  (Polychromatic418967fa.accept_11_7_9_2_1_260 62 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 233 (accept_3_2 61 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 233 (accept_3_2 58 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 233 (accept_3_2 55 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 233 (Polychromatic418967fa.accept_19_16_10_5_1_7106 54 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 233 (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 233 (accept_3_2 52 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 50 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 233 (accept_3_2 49 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 233 (accept_3_2 46 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 233 (accept_3_2 43 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 233 (Polychromatic418967fa.accept_19_3_10_5_1_4314 41 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 233 (accept_3_2 40 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 233 (accept_3_2 37 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 233 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 233 (accept_3_2 34 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 233 (accept_3_2 31 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 233 (accept_3_2 28 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 233 (accept_3_2 25 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 233 (accept_3_2 22 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 233 (accept_3_2 19 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 233 (accept_3_2 16 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 233
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 233 (accept_3_2 13 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 233 (accept_3_2 10 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 233 (accept_3_2 7 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 86 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 233 (accept_3_2 4 86 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 233 (accept_3_2 1 86 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 233
  (allA_of_3_0 85 85 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 233 (allA_succ_of_accept 83 84 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 233 (accept_3_2 82 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 233 (Polychromatic418967fa.accept_17_13_16_12_1_6562 81 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 80 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 233 (accept_3_2 79 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 84 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 233 (accept_3_2 76 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 233 (accept_3_2 73 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 233
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 71 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 233 (accept_3_2 70 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 233 (accept_3_2 67 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 233 (Polychromatic418967fa.accept_23_20_15_3_1_13909 66 84 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 233 (accept_3_2 64 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 62 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 233 (accept_3_2 61 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 233 (accept_3_2 58 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 233 (accept_3_2 55 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 233 (accept_3_2 52 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 233 (accept_3_2 49 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 233 (accept_3_2 46 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 233 (accept_3_2 43 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 84 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 233 (accept_3_2 40 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 233 (accept_3_2 37 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 233
  (Polychromatic418967fa.accept_17_1_16_12_1_5298 35 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 233 (accept_3_2 34 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 233 (accept_3_2 31 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 233 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 233 (accept_3_2 28 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 233 (Polychromatic418967fa.accept_25_1_9_8_1_13908 26 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 233 (accept_3_2 25 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 233 (accept_3_2 22 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 233 (accept_3_2 19 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 233
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 233 (accept_3_2 16 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 233 (accept_3_2 13 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 233 (Polychromatic418967fa.accept_16_12_4_9_1_4633 12 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 233 (accept_3_2 10 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 233 (Polychromatic418967fa.accept_16_8_4_9_1_4666 8 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 233 (accept_3_2 7 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 233 (accept_3_2 4 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 84 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 233 (accept_3_2 1 84 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 233
  (allA_succ_of_accept 82 83 233 (accept_3_2 82 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 233 (accept_3_2 79 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 233 (accept_3_2 76 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 233 (accept_3_2 73 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 233 (accept_3_2 70 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 233 (accept_3_2 67 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 233
  (Polychromatic418967fa.accept_17_14_15_12_1_1921 65 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 83 233 (accept_3_2 64 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 83 233 (Polychromatic418967fa.accept_19_6_7_5_1_256 63 83 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 233 (accept_3_2 61 83 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60
  83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 233 (accept_3_2 58 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 233 (accept_3_2 55 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 233 (accept_3_2 52 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 233 (accept_3_2 49 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 233
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 233 (accept_3_2 46 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 233 (Polychromatic418967fa.accept_16_12_3_9_1_5886 44 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 233 (accept_3_2 43 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 233 (accept_3_2 40 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 233 (accept_3_2 37 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 233
  (Polychromatic418967fa.accept_17_1_15_12_1_7907 35 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 233 (accept_3_2 34 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 233 (accept_3_2 31 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 233 (accept_3_2 28 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 233 (accept_3_2 25 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 233 (accept_3_2 22 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 233 (accept_3_2 19 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 233 (accept_3_2 16 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 233 (accept_3_2 13 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 233 (accept_3_2 10 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 233 (Polychromatic418967fa.accept_19_9_7_5_1_9887 9 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 233 (accept_3_2 7 83 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 233 (accept_3_2 4 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 233 (accept_3_2 1 83 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 233 (allA_of_3_0 82 82 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 233
  (allA_succ_of_accept 80 81 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 233 (accept_3_2 79 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 233 (Polychromatic418967fa.accept_15_2_6_8_1_754
  77 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 233 (accept_3_2 76
  81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 233 (accept_3_2 73 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 233
  (Polychromatic418967fa.accept_43_28_38_18_1_13907 71 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 81 233 (accept_3_2 70 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 81 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 233 (accept_3_2 67 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 233 (Polychromatic418967fa.accept_16_2_1_9_1_2577
  66 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 233
  (Polychromatic418967fa.accept_23_19_12_3_1_13906 65 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 81 233 (accept_3_2 64 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 81 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 233 (accept_3_2 61 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 233
  (Polychromatic418967fa.accept_23_14_12_3_1_13905 60 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 59 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 233 (accept_3_2 58 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 233 (Polychromatic418967fa.accept_21_15_18_2_1_6376 57 81
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 233 (accept_3_2 55 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 233 (accept_3_2 52 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 233 (accept_3_2 49 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 233 (accept_3_2 46 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 233 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 233 (accept_3_2 43 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 233 (accept_3_2 40 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 233 (accept_3_2 37 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 233 (Polychromatic418967fa.accept_21_15_18_2_1_6376 36 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 233 (accept_3_2 34 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 233 (accept_3_2 31 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 233 (accept_3_2 28 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 233 (accept_3_2 25 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 233 (Polychromatic418967fa.accept_16_8_1_9_1_847 24 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 233 (Polychromatic418967fa.accept_20_3_1_13_1_6742 23 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 233 (accept_3_2 22 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 233 (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 233 (accept_3_2 19 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 233 (accept_3_2 16 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 233 (accept_3_2 13 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 233 (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 233 (accept_3_2 10 81 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 233 (accept_3_2 7 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 233 (accept_3_2 4 81 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 233 (accept_3_2 1 81 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 233
  (allA_succ_of_accept 79 80 233 (accept_3_2 79 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 233 (Polychromatic418967fa.accept_18_5_8_17_1_3478 77 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 233 (accept_3_2 76 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 233 (accept_3_2 73 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 233 (Polychromatic418967fa.accept_15_12_5_8_1_5247 72 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 233 (accept_3_2 70 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 233 (accept_3_2 67 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 233 (Polychromatic418967fa.accept_19_8_4_5_1_8569 65 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 233 (accept_3_2 64 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 233 (accept_3_2 61 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 233 (Polychromatic418967fa.accept_22_16_14_13_1_10858 60 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 233 (accept_3_2 58 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 233 (accept_3_2 55 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 233 (accept_3_2 52 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 233 (accept_3_2 49 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 233 (accept_3_2 46 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 233
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 44 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 233 (accept_3_2 43 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 233 (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 233 (accept_3_2 40 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 233 (accept_3_2 37 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 233 (Polychromatic418967fa.accept_21_14_17_2_1_11069 35 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 233 (accept_3_2 34 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 233
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 233 (accept_3_2 31 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 233 (accept_3_2 28 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 233 (accept_3_2 25 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 233 (Polychromatic418967fa.accept_21_3_17_2_1_11043 24 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 233 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 233 (accept_3_2 22 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 233 (accept_3_2 19 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 233 (accept_3_2 16 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 233 (accept_3_2 13 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 233 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 233 (accept_3_2 10 80 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 233 (accept_3_2 7 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 233 (accept_3_2 4 80 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  80 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 233 (accept_3_2 1 80 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 233 (allA_of_3_0 79
  79 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 233 (allA_succ_of_accept 77 78 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 233 (accept_3_2 76 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 233 (accept_3_2 73 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 233 (accept_3_2 70 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 233 (accept_3_2 67 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 233 (accept_3_2 64 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 233 (accept_3_2 61 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 233 (Polychromatic418967fa.accept_19_3_2_5_1_5679 60 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 233 (accept_3_2 58 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 233 (accept_3_2 55 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 233
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 53 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 233 (accept_3_2 52 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 233 (accept_3_2 49 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 233 (accept_3_2 46 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 233 (Polychromatic418967fa.accept_28_16_22_9_1_13904 44 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 233 (accept_3_2 43 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 78
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 233 (accept_3_2 40 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 233 (accept_3_2 37 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 233 (accept_3_2 34 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 233 (Polychromatic418967fa.accept_18_15_6_17_1_2386 33 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 233 (accept_3_2 31 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 233 (accept_3_2 28 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 233 (accept_3_2 25 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 233 (accept_3_2 22 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 233 (accept_3_2 19 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 233 (Polychromatic418967fa.accept_19_18_2_5_1_5682 18 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 233 (accept_3_2 16 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 233 (accept_3_2 13 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 233 (accept_3_2 10 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 233 (Polychromatic418967fa.accept_17_8_10_12_1_5335 8 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 233 (accept_3_2 7 78 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 233 (accept_3_2 4 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 233 (accept_3_2 1 78 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 233 (allA_succ_of_accept 76 77 233 (accept_3_2 76 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 233 (accept_3_2 73 77 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 233 (Polychromatic418967fa.accept_14_2_7_9_1_2937
  72 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 233
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 71 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 233 (accept_3_2 70 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 233 (accept_3_2 67 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 233 (accept_3_2 64 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 233 (Polychromatic418967fa.accept_19_6_1_5_1_5719 63 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 233 (Polychromatic418967fa.accept_18_8_5_17_1_1388 62 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 233 (accept_3_2 61 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 233
  (Polychromatic418967fa.accept_21_17_14_2_1_4762 59 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 233 (accept_3_2 58 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 233 (accept_3_2 55 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 233
  (Polychromatic418967fa.accept_16_5_13_9_1_2594 53 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 233 (accept_3_2 52 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 233 (Polychromatic418967fa.accept_19_12_1_5_1_9924 50 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 233 (accept_3_2 49 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 233 (accept_3_2 46 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 233 (accept_3_2 43 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 233
  (Polychromatic418967fa.accept_19_3_1_5_1_8549 41 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 233 (accept_3_2 40 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 233 (accept_3_2 37 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 233 (accept_3_2 34 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 233 (Polychromatic418967fa.accept_21_11_14_2_1_6371 32 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 233 (accept_3_2 31 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 233 (accept_3_2 28 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 233 (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 233 (accept_3_2 25 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 233
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 23 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 233 (accept_3_2 22 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 233 (accept_3_2 19 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 233 (Polychromatic418967fa.accept_19_18_1_5_1_5720 18 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 233
  (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 233 (accept_3_2 16 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 233 (accept_3_2 13 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 233 (accept_3_2 10 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 233 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 233 (accept_3_2 7 77 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 233 (accept_3_2 4 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 233 (accept_3_2 1 77 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 233 (allA_of_3_0 76 76 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 233 (allA_succ_of_accept 74 75
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 233 (accept_3_2 73 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 71 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 233 (accept_3_2 70 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 233 (accept_3_2 67 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 233 (accept_3_2 64 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 233 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 75 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 233 (accept_3_2 61 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 233 (accept_3_2 58 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 233 (accept_3_2 55 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 233 (accept_3_2 52 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 233 (accept_3_2 49 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 233 (accept_3_2 46 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 233 (accept_3_2 43 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 233 (accept_3_2 40 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 233 (accept_3_2 37 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 233 (Polychromatic418967fa.accept_16_4_11_9_1_1631 36 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 233 (accept_3_2 34 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 233 (accept_3_2 31 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 233 (accept_3_2 28 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 233 (accept_3_2 25 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 233 (accept_3_2 22 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 233 (accept_3_2 19 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 233 (accept_3_2 16 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 233 (accept_3_2 13 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 233 (accept_3_2 10 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 233 (accept_3_2 7 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 233 (accept_3_2 4 75 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 233 (accept_3_2 1 75 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 233 (allA_succ_of_accept
  73 74 233 (accept_3_2 73 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 233
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 233 (accept_3_2 70 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 68
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 233 (accept_3_2 67 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 233 (accept_3_2 64 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 233 (accept_3_2 61 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 233 (accept_3_2 58 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 233 (accept_3_2 55
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 233 (Polychromatic418967fa.accept_17_2_6_12_1_7912 53 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 233 (accept_3_2 52 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 233 (accept_3_2 49 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 233 (accept_3_2 46 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 233 (accept_3_2 43
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 233 (accept_3_2 40 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 233 (Polychromatic418967fa.accept_11_5_8_2_1_588
  38 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 233 (accept_3_2 37
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 233
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 233 (accept_3_2 34 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 233 (accept_3_2 31 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 233 (accept_3_2 28 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 233 (accept_3_2 25 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 233 (accept_3_2 22 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 233 (accept_3_2 19 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 233
  (Polychromatic418967fa.accept_17_1_6_12_1_1944 18 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 233 (accept_3_2 16 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 233 (accept_3_2 13 74
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 233 (accept_3_2 10 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 233 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 233 (accept_3_2 7 74 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 233 (accept_3_2 4 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 233 (accept_3_2 1 74 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  233 (allA_of_3_0 73 73 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 233 (allA_succ_of_accept 71 72 233
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 233 (accept_3_2 70 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 69 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 233 (Polychromatic418967fa.accept_16_4_8_9_1_4639 68 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 233 (accept_3_2 67 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 233 (Polychromatic418967fa.accept_19_9_15_5_1_5666 66 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 65 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 233 (accept_3_2 64 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 233 (accept_3_2 61 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 233 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 233
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 233 (accept_3_2 58 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 57 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 233 (accept_3_2 55 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 233 (Polychromatic418967fa.accept_21_12_9_2_1_7941 54 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 233
  (Polychromatic418967fa.accept_14_11_2_9_1_5873 53 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 233 (accept_3_2 52 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 233 (accept_3_2 49 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 72 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 233
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 47 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 233 (accept_3_2 46 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 233 (accept_3_2 43 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 233 (Polychromatic418967fa.accept_17_8_4_12_1_1994 42 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 233
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 233 (accept_3_2 40 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 233 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 233 (Polychromatic418967fa.accept_21_17_9_2_1_13903 38 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 233 (accept_3_2 37 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 233 (accept_3_2 34 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 233 (accept_3_2 31 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 233
  (Polychromatic418967fa.accept_19_10_15_5_1_5698 29 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 233 (accept_3_2 28 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 233 (Polychromatic418967fa.accept_21_6_9_2_1_9554 27 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 233 (accept_3_2 25 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 233
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 233 (accept_3_2 22 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 233 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 233 (accept_3_2 19 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 233
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 233 (accept_3_2 16 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 233 (Polychromatic418967fa.accept_21_14_9_2_1_8005 14 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 233 (accept_3_2 13 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 233 (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 72
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 233
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 233 (accept_3_2 10 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 233 (Polychromatic418967fa.accept_17_9_4_12_1_2958 9 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 233 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 233 (accept_3_2 7 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 72 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 233 (accept_3_2 4 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  233 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 72 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 233 (Polychromatic418967fa.accept_17_2_4_12_1_6587 2 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 233 (accept_3_2 1 72 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 233 (allA_succ_of_accept 70 71 233 (accept_3_2 70 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 71 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 71 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 233 (accept_3_2 67 71 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 233 (accept_3_2 64 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 233 (accept_3_2 61 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 233 (Polychromatic418967fa.accept_19_3_14_5_1_8597 60 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 233 (accept_3_2 58 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 233 (Polychromatic418967fa.accept_16_8_7_9_1_7052 56 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 233 (accept_3_2 55 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 233
  (Polychromatic418967fa.accept_24_5_23_17_1_13887 53 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 71 233 (accept_3_2 52 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 71 233 (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 71 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 233 (accept_3_2 49 71 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48
  71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 233
  (Polychromatic418967fa.accept_19_9_14_5_1_1890 47 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 233 (accept_3_2 46 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 233 (accept_3_2 43 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 233 (accept_3_2 40 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 233 (Polychromatic418967fa.accept_25_14_21_8_1_13902 39 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 233 (accept_3_2 37 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 233 (accept_3_2 34 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 233 (accept_3_2 31 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 233
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 233 (accept_3_2 28 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 233 (accept_3_2 25 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 233
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 233 (accept_3_2 22 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 233 (Polychromatic418967fa.accept_19_2_14_5_1_5715 21 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 233 (accept_3_2 19 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 233 (accept_3_2 16 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 233 (accept_3_2 13 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 233
  (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 233 (accept_3_2 10 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 233 (Polychromatic418967fa.accept_19_9_14_5_1_1890 9 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 233 (accept_3_2 7 71 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 233
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 233 (accept_3_2 4 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 233 (accept_3_2 1 71 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 233
  (allA_of_3_0 70 70 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 233 (allA_succ_of_accept 68 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 233 (accept_3_2 67 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 233 (accept_3_2 64 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 233 (accept_3_2 61 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 233 (accept_3_2 58 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 233 (accept_3_2 55 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 233 (accept_3_2 52 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 233 (accept_3_2 49 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 233 (accept_3_2 46 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 233 (accept_3_2 43 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 233 (accept_3_2 40 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 233 (accept_3_2 37 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 233 (Polychromatic418967fa.accept_19_16_12_5_1_8578 35 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 233 (accept_3_2 34 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 233 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 69
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 233 (accept_3_2 31 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 233 (accept_3_2 28 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 233 (accept_3_2 25 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 233 (accept_3_2 22 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 233 (accept_3_2 19 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 233 (accept_3_2 16 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 233 (accept_3_2 13 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 233 (accept_3_2 10 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 233 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 69 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 233 (accept_3_2 7 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  233 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 69 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 233 (accept_3_2 4 69 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 233 (accept_3_2 1 69 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 233 (allA_succ_of_accept 67 68
  233 (accept_3_2 67 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 233 (accept_3_2 64 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 233 (Polychromatic418967fa.accept_12_2_8_5_1_408
  62 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 233 (accept_3_2 61
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 233 (accept_3_2 58 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 233 (accept_3_2 55 68
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 233
  (Polychromatic418967fa.accept_13_2_3_12_1_735 54 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 233 (accept_3_2 52 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 233 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 233 (accept_3_2 49
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 233
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 233 (accept_3_2 46 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 233 (Polychromatic418967fa.accept_16_12_4_9_1_4633
  44 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 233 (accept_3_2 43
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 233
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 41 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 233 (accept_3_2 40 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 233 (accept_3_2 37 68
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 233 (accept_3_2 34 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 233 (accept_3_2 31 68
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 233 (Polychromatic418967fa.accept_9_3_5_8_1_99
  30 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 233 (accept_3_2 28 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 233 (accept_3_2 25 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 233
  (Polychromatic418967fa.accept_20_3_8_13_1_3832 23 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 233 (accept_3_2 22 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 233 (accept_3_2 19 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 233 (accept_3_2 16 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 233 (accept_3_2 13 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 233 (accept_3_2 10 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 233 (Polychromatic418967fa.accept_16_8_4_9_1_4666 8 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 233 (accept_3_2 7 68 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 233 (accept_3_2 4 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 233 (accept_3_2 1 68 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 233
  (allA_of_3_0 67 67 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 233 (allA_succ_of_accept 65 66 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 233 (accept_3_2 64 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 233 (accept_3_2 61 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 233 (accept_3_2 58 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 233 (accept_3_2 55 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 233
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 53 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 233 (accept_3_2 52 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 233 (accept_3_2 49 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 233 (accept_3_2 46 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 233 (Polychromatic418967fa.accept_18_9_12_17_1_6060 45 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 233 (accept_3_2 43 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 233 (accept_3_2 40 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 233 (accept_3_2 37 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 233 (accept_3_2 34 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 233 (accept_3_2 31 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 233 (Polychromatic418967fa.accept_21_9_3_2_1_6363 30 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 233 (accept_3_2 28 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 233 (accept_3_2 25 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 233 (accept_3_2 22 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 233 (accept_3_2 19 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 233 (accept_3_2 16 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 233 (accept_3_2 13 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 233 (accept_3_2 10 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 233 (accept_3_2 7 66 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 233 (accept_3_2 4 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 66 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 233 (accept_3_2 1 66 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 233
  (allA_succ_of_accept 64 65 233 (accept_3_2 64 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 62 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 233 (accept_3_2 61 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 233 (accept_3_2 58 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 233 (accept_3_2 55 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 233 (Polychromatic418967fa.accept_19_16_8_5_1_4322 54 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 233
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 233 (accept_3_2 52 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 233 (accept_3_2 49 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 233 (accept_3_2 46 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 233 (accept_3_2 43 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 233 (accept_3_2 40 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 38 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 233 (accept_3_2 37 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 233 (Polychromatic418967fa.accept_22_14_21_13_1_13901 36 65 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 233
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 35 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 233 (accept_3_2 34 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 233 (accept_3_2 31 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 233 (accept_3_2 28 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 233 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 233 (accept_3_2 25 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 233 (accept_3_2 22 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 233 (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 233 (accept_3_2 19 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 65 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 233 (accept_3_2 16 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 233 (accept_3_2 13 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 233 (accept_3_2 10 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 233 (Polychromatic418967fa.accept_17_9_14_12_1_9177 9 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 233 (accept_3_2 7 65 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 233 (accept_3_2 4 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 65 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 233 (accept_3_2 1 65 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 233
  (allA_of_3_0 64 64 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 233 (allA_succ_of_accept 62 63 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 233 (accept_3_2 61 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 59 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 233 (accept_3_2 58 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 233 (accept_3_2 55 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 233 (accept_3_2 52 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 233 (Polychromatic418967fa.accept_18_15_9_17_1_6043 51 63
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 233 (accept_3_2 49 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 233 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 233 (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 233 (accept_3_2 46 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 233 (accept_3_2 43 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 233 (Polychromatic418967fa.accept_15_11_3_8_1_750 41 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 233 (accept_3_2 40 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 233 (accept_3_2 37 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 233 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 233 (accept_3_2 34 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 233 (accept_3_2 31 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 233 (Polychromatic418967fa.accept_22_7_19_13_1_10815 29 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 233 (accept_3_2 28 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 63 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 233 (accept_3_2 25 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 233 (accept_3_2 22 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 233 (accept_3_2 19 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 233 (accept_3_2 16 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 233 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 63
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 233 (accept_3_2 13 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 233 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 233 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 233 (accept_3_2 10 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 233 (accept_3_2 7 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 63 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 233 (accept_3_2 4 63 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 233 (Polychromatic418967fa.accept_19_3_6_5_1_9947 3 63 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 233 (accept_3_2 1 63 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 233 (allA_succ_of_accept 61 62 233
  (accept_3_2 61 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 233 (accept_3_2 58 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 233 (accept_3_2 55
  62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 233
  (Polychromatic418967fa.accept_13_2_10_12_1_757 54 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 233 (accept_3_2 52 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 233 (accept_3_2 49 62
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 233
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 233 (accept_3_2 46 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 233 (accept_3_2 43
  62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 233
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 233 (accept_3_2 40 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 233 (accept_3_2 37 62
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 233 (Polychromatic418967fa.accept_7_1_6_2_1_18
  36 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 233 (accept_3_2 34 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 233 (accept_3_2 31 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 233 (Polychromatic418967fa.accept_17_13_11_12_1_4131 30 62 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 233 (accept_3_2 28 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 233 (Polychromatic418967fa.accept_21_5_20_2_1_7948 26 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 233 (accept_3_2 25 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 233 (accept_3_2 22 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 233 (accept_3_2 19 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 233 (accept_3_2 16 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 233 (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 233 (accept_3_2 13 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 233 (Polychromatic418967fa.accept_27_12_8_17_1_13900 12 62
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 233 (accept_3_2 10 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 233 (accept_3_2 7 62 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 62 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 233 (accept_3_2 4 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 233 (accept_3_2 1 62 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 233
  (allA_of_3_0 61 61 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 233 (allA_succ_of_accept 59 60 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 233 (accept_3_2 58 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 233 (accept_3_2 55 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 233 (accept_3_2 52 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 233 (Polychromatic418967fa.accept_16_3_12_9_1_8250 51 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 233 (accept_3_2 49 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 233 (accept_3_2 46 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 233 (accept_3_2 43 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 233 (Polychromatic418967fa.accept_24_18_12_17_1_10620 42 60
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 233 (accept_3_2 40 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 233 (accept_3_2 37 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 233 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 233
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 233 (accept_3_2 34 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 233 (accept_3_2 31 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 233 (accept_3_2 28 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 233 (accept_3_2 25 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 233 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 233 (accept_3_2 22 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 233 (accept_3_2 19 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 233
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 233 (accept_3_2 16 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 233 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 233 (accept_3_2 13 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 233 (accept_3_2 10 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 233 (accept_3_2 7 60 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 233 (accept_3_2 4 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 233 (accept_3_2 1 60 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 233
  (allA_succ_of_accept 58 59 233 (accept_3_2 58 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 233 (accept_3_2 55 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 233
  (Polychromatic418967fa.accept_11_9_4_2_1_600 53 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 233 (accept_3_2 52 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 233 (accept_3_2 49 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 233 (accept_3_2 46 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 233 (accept_3_2 43 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 233 (accept_3_2 40 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 233 (accept_3_2 37 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 233 (accept_3_2 34 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 233 (accept_3_2 31 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 233 (accept_3_2 28 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 233 (accept_3_2 25 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 233
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 233 (accept_3_2 22 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 233 (accept_3_2 19 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 233
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 233 (accept_3_2 16 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 233 (accept_3_2 13 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 233 (accept_3_2 10 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 233 (accept_3_2 7 59 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 233 (accept_3_2 4 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 233 (accept_3_2 1 59 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 233 (allA_of_3_0
  58 58 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 233 (allA_succ_of_accept 56 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 233 (accept_3_2 55 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 53 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 233 (accept_3_2 52 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 233 (accept_3_2 49 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 233 (accept_3_2 46 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 233 (accept_3_2 43 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 233 (accept_3_2 40 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 233 (accept_3_2 37 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 233 (accept_3_2 34 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 233 (accept_3_2 31 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 233 (accept_3_2 28 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 233 (accept_3_2 25 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 233 (accept_3_2 22 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 233 (accept_3_2 19 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 233 (accept_3_2 16 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 233 (accept_3_2 13 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 233 (Polychromatic418967fa.accept_23_12_11_3_1_13899 12 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 233 (accept_3_2 10 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 233 (Polychromatic418967fa.accept_21_9_15_2_1_4765 9 57 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 233 (accept_3_2 7 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 57 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 233 (accept_3_2 4 57 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 233 (accept_3_2 1 57 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 233 (allA_succ_of_accept 55 56 233 (accept_3_2 55 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 56 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 233 (Polychromatic418967fa.accept_21_11_14_2_1_6371 53 56
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 233 (accept_3_2 52 56 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 233 (accept_3_2 49 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 233 (accept_3_2 46 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 233
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 233 (accept_3_2 43 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 233 (accept_3_2 40 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 233 (accept_3_2 37 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 233 (accept_3_2 34 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 233 (accept_3_2 31 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 233 (accept_3_2 28 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 233 (accept_3_2 25 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 233 (accept_3_2 22 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 233
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 233 (accept_3_2 19 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 233 (accept_3_2 16 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 233 (accept_3_2 13 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 233 (accept_3_2 10 56 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 233 (accept_3_2 7 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 233 (accept_3_2 4 56 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 233 (accept_3_2 1 56 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 233 (allA_of_3_0 55 55 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 233
  (allA_succ_of_accept 53 54 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 233 (accept_3_2 52 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 233 (Polychromatic418967fa.accept_16_2_6_9_1_3473
  50 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 233 (accept_3_2 49
  54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 233
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 233 (accept_3_2 46 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301
  44 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 233 (accept_3_2 43
  54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 233
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 233 (Polychromatic418967fa.accept_17_7_3_12_1_4098 41 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 233 (accept_3_2 40 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 233 (accept_3_2 37 54
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 233
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 233 (accept_3_2 34 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 233 (accept_3_2 31 54
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 233
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 233 (accept_3_2 28 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 233
  (Polychromatic418967fa.accept_29_26_25_1_1_13898 26 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 54 233 (accept_3_2 25 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 54 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 233 (accept_3_2 22 54 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 233 (Polychromatic418967fa.accept_14_7_12_9_1_2926
  21 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 233
  (Polychromatic418967fa.accept_19_1_16_5_1_5671 20 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 233 (accept_3_2 19 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 233 (accept_3_2 16 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 233
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 233 (accept_3_2 13 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 233 (accept_3_2 10 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 54 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 233
  (Polychromatic418967fa.accept_17_8_3_12_1_5354 8 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 233 (accept_3_2 7 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 233 (accept_3_2 4 54 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 233
  (Polychromatic418967fa.accept_15_2_9_8_1_736 2 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 233 (accept_3_2 1 54 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 233 (allA_succ_of_accept 52 53 233 (accept_3_2
  52 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 233
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 50 53 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 233 (accept_3_2 49 53 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 233 (accept_3_2 46 53
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 233
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 233 (accept_3_2 43 53 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 233 (Polychromatic418967fa.accept_19_4_15_5_1_3043 42 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 233 (accept_3_2 40 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 233 (Polychromatic418967fa.accept_19_1_15_5_1_4357 39 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 233 (Polychromatic418967fa.accept_17_4_2_12_1_6554 38 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 233 (accept_3_2 37 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 233
  (Polychromatic418967fa.accept_21_14_11_2_1_13897 35 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 53 233 (accept_3_2 34 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 53 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 233 (Polychromatic418967fa.accept_22_10_9_13_1_9247 32 53
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 233 (accept_3_2 31 53 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 233 (Polychromatic418967fa.accept_14_2_11_9_1_2925
  30 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 233
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 233 (accept_3_2 28 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 233 (accept_3_2 25 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 233
  (Polychromatic418967fa.accept_17_6_2_12_1_1992 23 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 233 (accept_3_2 22 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 233 (accept_3_2 19 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 233
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 233 (accept_3_2 16 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 233 (Polychromatic418967fa.accept_16_14_5_9_1_5901 14 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 233 (accept_3_2 13 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 233
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 233 (accept_3_2 10 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 233 (Polychromatic418967fa.accept_19_9_15_5_1_5666 9 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 233 (accept_3_2 7 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 233 (accept_3_2 4 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  233 (Polychromatic418967fa.accept_34_3_19_29_1_13896 3 53 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 233 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 233 (accept_3_2 1 53 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 233))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 233
  (allA_of_3_0 52 52 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 233 (allA_succ_of_accept 50 51 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 233 (accept_3_2 49 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 233 (accept_3_2 46 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 233 (accept_3_2 43 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 233 (accept_3_2 40 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 233 (accept_3_2 37 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 233 (Polychromatic418967fa.accept_21_15_9_2_1_7973 36 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 233 (Polychromatic418967fa.accept_20_15_11_13_1_11192 35 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 233 (accept_3_2 34 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 233 (accept_3_2 31 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 233 (accept_3_2 28 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 233 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 233 (accept_3_2 25 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 233 (Polychromatic418967fa.accept_18_6_15_17_1_7363 24 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 233 (accept_3_2 22 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 233 (accept_3_2 19 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 233 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 233 (accept_3_2 16 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 233 (Polychromatic418967fa.accept_20_15_11_13_1_11192 15 51 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 233 (accept_3_2 13 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 233 (accept_3_2 10 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 51 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 233 (accept_3_2 7 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 233 (accept_3_2 4 51 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 233 (accept_3_2 1 51 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 233)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 233 (allA_succ_of_accept 49 50 233 (accept_3_2 49 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 233 (accept_3_2 46 50 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 233 (accept_3_2 43 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 233 (accept_3_2 40 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 233 (accept_3_2 37 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 233 (accept_3_2 34 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 233 (accept_3_2 31 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 233 (accept_3_2 28 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 233
  (Polychromatic418967fa.accept_11_4_6_2_1_51 26 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 233 (accept_3_2 25 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 233 (accept_3_2 22 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 233 (accept_3_2 19 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 233 (accept_3_2 16 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 233
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 233 (accept_3_2 13 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 233 (accept_3_2 10 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 233 (accept_3_2 7 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 50 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 233 (Polychromatic418967fa.accept_20_5_10_13_1_6754 5 50 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 233 (accept_3_2 4 50 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 233 (accept_3_2 1 50 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 233)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 233 (allA_of_3_0 49 49 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 233 (allA_succ_of_accept 47 48
  233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 233 (accept_3_2 46 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 233 (Polychromatic418967fa.accept_28_16_20_9_1_13895 44 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 233 (accept_3_2 43 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 233 (accept_3_2 40 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 233 (accept_3_2 37 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 233
  (Polychromatic418967fa.accept_10_5_8_3_1_229 35 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 233 (accept_3_2 34 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 233 (accept_3_2 31 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 233 (Polychromatic418967fa.accept_19_11_10_5_1_5662 30 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 233 (accept_3_2 28 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 233 (accept_3_2 25 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 233 (accept_3_2 22 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 233 (accept_3_2 19 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 233 (accept_3_2 16 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 233 (accept_3_2 13 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 233 (accept_3_2 10 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 233 (accept_3_2 7 48 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 233 (accept_3_2 4 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 233 (accept_3_2 1 48 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 233)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 233 (allA_succ_of_accept 46
  47 233 (accept_3_2 46 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 233 (accept_3_2 43 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 233 (accept_3_2 40 47
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 233 (accept_3_2 37 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 233 (Polychromatic418967fa.accept_10_5_7_3_1_561
  35 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 233 (accept_3_2 34
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 233 (accept_3_2 31 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 233 (Polychromatic418967fa.accept_21_8_5_2_1_8004
  29 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 233 (accept_3_2 28
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 233
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 233 (accept_3_2 25 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 233 (accept_3_2 22 47
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 233 (accept_3_2 19 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 233 (accept_3_2 16 47
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 233 (accept_3_2 13 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 233 (accept_3_2 10 47
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 233
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 233 (Polychromatic418967fa.accept_16_8_15_9_1_4676 8 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 233 (accept_3_2 7 47 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 233 (accept_3_2 4 47 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 233 (accept_3_2 1 47 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  233))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 233 (allA_of_3_0 46 46 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 233 (allA_succ_of_accept 44 45 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 233 (accept_3_2 43 45 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  42 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 233 (accept_3_2 40 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 233 (accept_3_2 37 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 233
  (Polychromatic418967fa.accept_20_15_5_13_1_13894 35 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 233 (accept_3_2 34 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 233 (accept_3_2 31 45 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 233
  (Polychromatic418967fa.accept_17_13_11_12_1_4131 30 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 233 (accept_3_2 28 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 233 (accept_3_2 25 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 233 (Polychromatic418967fa.accept_26_24_19_25_1_13893 24 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 233 (accept_3_2 22 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 233 (accept_3_2 19 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 233 (accept_3_2 16 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 233 (accept_3_2 13 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 233 (Polychromatic418967fa.accept_23_11_22_3_1_13892 11 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 233 (accept_3_2 10 45 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 233 (Polychromatic418967fa.accept_19_9_7_5_1_9887 9 45 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 233 (accept_3_2 7 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 233 (accept_3_2 4 45 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 45 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 233 (accept_3_2 1 45 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 233))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  233 (allA_succ_of_accept 43 44 233 (accept_3_2 43 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 233 (Polychromatic418967fa.accept_17_8_10_12_1_5335 42 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 233 (accept_3_2 40 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 233 (accept_3_2 37 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 233 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 233 (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 233 (accept_3_2 34 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 233
  (Polychromatic418967fa.accept_13_6_5_12_1_307 32 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 233 (accept_3_2 31 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 233 (accept_3_2 28 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 233 (accept_3_2 25 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 24 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 233 (Polychromatic418967fa.accept_17_6_10_12_1_4129 23 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 233 (accept_3_2 22 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 233
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 233 (accept_3_2 19 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 233 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 233 (accept_3_2 16 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 233 (accept_3_2 13 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 233 (Polychromatic418967fa.accept_24_12_20_17_1_13891 12 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 233 (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 233 (accept_3_2 10 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 233
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 233 (accept_3_2 7 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  233 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 44 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 233 (accept_3_2 4 44 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 44 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 44 233 (accept_3_2 1 44 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  233)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 233 (allA_of_3_0 43 43 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 233 (allA_succ_of_accept 41 42 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 233 (accept_3_2 40 42 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 233 (accept_3_2 37 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  42 233 (Polychromatic418967fa.accept_24_12_18_17_1_12249 36 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 233 (accept_3_2 34 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 233 (accept_3_2 31 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  42 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 42 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 233 (accept_3_2 28 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 233 (accept_3_2 25 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  42 233 (Polychromatic418967fa.accept_26_24_16_25_1_13890 24 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 233 (accept_3_2 22 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 233 (accept_3_2 19 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  42 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 42 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 233 (accept_3_2 16 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 233 (accept_3_2 13 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  42 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 233 (accept_3_2 10 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 233
  (Polychromatic418967fa.accept_19_8_4_5_1_8569 8 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 42 233 (accept_3_2 7 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42
  233 (Polychromatic418967fa.accept_19_6_4_5_1_5650 6 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 42 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 233 (accept_3_2 4 42 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 233 (accept_3_2 1 42 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  233)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 233 (allA_succ_of_accept 40 41 233 (accept_3_2 40 41 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 233 (accept_3_2 37 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 233 (accept_3_2 34 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 233 (accept_3_2 31 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 233 (accept_3_2 28 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 233
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 233 (accept_3_2 25 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 233 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 233 (accept_3_2 22 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 233 (accept_3_2 19 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 233 (accept_3_2 16 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 233
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 233 (accept_3_2 13 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 233 (accept_3_2 10 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 233 (Polychromatic418967fa.accept_21_9_20_2_1_8000 9 41 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 233 (accept_3_2 7 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 233 (accept_3_2 4 41 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 233 (accept_3_2 1 41 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 233))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 233
  (allA_of_3_0 40 40 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 233 (allA_succ_of_accept 38 39 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 233 (accept_3_2 37 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 233 (Polychromatic418967fa.accept_16_3_7_9_1_3474 35 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 233 (accept_3_2 34 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 233 (accept_3_2 31 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 233 (accept_3_2 28 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 233 (accept_3_2 25 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 233 (accept_3_2 22 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 233 (accept_3_2 19 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 233 (Polychromatic418967fa.accept_15_2_9_8_1_736 17 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 233 (accept_3_2 16 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 233 (accept_3_2 13 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 233 (accept_3_2 10 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 233 (accept_3_2 7 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 233 (accept_3_2 4 39 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 233 (accept_3_2 1 39 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 233))))))))))))))))))))))))))))))))))))))) (allB_succ 38 233
  (allA_succ_of_accept 37 38 233 (accept_3_2 37 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 233 (accept_3_2 34 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 233 (accept_3_2 31 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 233 (accept_3_2 28 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 233 (accept_3_2 25 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 233 (accept_3_2 22 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 233 (accept_3_2 19 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 233 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 233 (Polychromatic418967fa.accept_25_17_13_8_1_3187 17 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 233 (accept_3_2 16 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 233 (accept_3_2 13 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 233 (accept_3_2 10 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 233 (accept_3_2 7 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 233 (accept_3_2 4 38 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 233 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2
  38 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 233 (accept_3_2 1 38 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 233)))))))))))))))))))))))))))))))))))))) (allB_succ 37 233
  (allA_of_3_0 37 37 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 233 (allA_succ_of_accept 35 36 233
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 233 (accept_3_2 34 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 233 (accept_3_2 31 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 233 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 36
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 233 (accept_3_2 28 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 233 (Polychromatic418967fa.accept_19_7_17_5_1_3081 26 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 233 (accept_3_2 25 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 233 (accept_3_2 22 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 233 (accept_3_2 19 36 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 233 (accept_3_2 16 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 233 (accept_3_2 13 36 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 233 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 36 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 233
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 36 233 (accept_3_2 10 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 36 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 36 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 233 (accept_3_2 7 36 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 233 (accept_3_2 4 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 36 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 233 (accept_3_2 1 36 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 233)))))))))))))))))))))))))))))))))))) (allB_succ 35 233 (allA_succ_of_accept 34 35 233
  (accept_3_2 34 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 233
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 35 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 233 (accept_3_2 31 35 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062
  29 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 233 (accept_3_2 28
  35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 233 (accept_3_2 25 35 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 233 (Polychromatic418967fa.accept_21_3_14_2_1_7978 24 35 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 233
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 233 (accept_3_2 22 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 233 (Polychromatic418967fa.accept_19_1_16_5_1_5671 20 35 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 233 (accept_3_2 19 35 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 233 (accept_3_2 16 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 233 (Polychromatic418967fa.accept_17_15_1_12_1_7910 15 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 233 (accept_3_2 13 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 35 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 233 (accept_3_2 10 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 233 (Polychromatic418967fa.accept_21_9_14_2_1_6370 9 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 233 (accept_3_2 7 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 233
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 233 (accept_3_2 4 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 35 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 233 (accept_3_2 1 35 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 233))))))))))))))))))))))))))))))))))) (allB_succ 34 233 (allA_of_3_0 34 34 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 233 (allA_succ_of_accept 32 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 233 (accept_3_2 31 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 233 (accept_3_2 28 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 233 (accept_3_2 25 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 233 (accept_3_2 22 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 233 (accept_3_2 19 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 233 (accept_3_2 16 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 233 (accept_3_2 13 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 233 (accept_3_2 10 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 33 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 233 (accept_3_2 7 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 233 (accept_3_2 4 33 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 233 (accept_3_2 1 33 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  233))))))))))))))))))))))))))))))))) (allB_succ 32 233 (allA_succ_of_accept 31 32 233 (accept_3_2 31 32 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 233 (accept_3_2 28 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  32 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 233 (accept_3_2 25 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 233
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 233 (accept_3_2 22 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 233 (accept_3_2 19 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 32 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 233
  (Polychromatic418967fa.accept_21_17_11_2_1_7953 17 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 233 (accept_3_2 16 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 233 (accept_3_2 13 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 233 (accept_3_2 10 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 233 (Polychromatic418967fa.accept_19_8_13_5_1_1889 8 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 233 (accept_3_2 7 32 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 233 (accept_3_2 4 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 233 (accept_3_2 1 32 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 233)))))))))))))))))))))))))))))))) (allB_succ 31 233 (allA_of_3_0 31 31 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 233 (allA_succ_of_accept 29 30 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 233 (accept_3_2 28 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 233 (Polychromatic418967fa.accept_25_1_5_8_1_13889 26 30 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 233 (accept_3_2 25 30 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 233 (accept_3_2 22 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 233 (accept_3_2 19 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 30 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 233
  (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 233 (accept_3_2 16 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 233 (accept_3_2 13 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 233 (Polychromatic418967fa.accept_19_12_11_5_1_950 12 30 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 233 (accept_3_2 10 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 233 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 233 (accept_3_2 7 30 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 233 (accept_3_2 4 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 233 (accept_3_2 1 30 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 233)))))))))))))))))))))))))))))) (allB_succ 29 233 (allA_succ_of_accept 28 29 233
  (accept_3_2 28 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 233 (accept_3_2 25 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 233 (accept_3_2 22 29
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 233 (accept_3_2 19 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 233 (Polychromatic418967fa.accept_19_18_10_5_1_12639 18 29 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 233 (accept_3_2 16 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 233 (accept_3_2 13 29 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 233
  (Polychromatic418967fa.accept_19_11_10_5_1_5662 11 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 233 (accept_3_2 10 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 233 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 29 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 233 (accept_3_2 7 29 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 233 (accept_3_2 4 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 233 (Polychromatic418967fa.accept_13_2_3_12_1_735 2 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 233 (accept_3_2 1 29 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 233))))))))))))))))))))))))))))) (allB_succ 28 233 (allA_of_3_0 28 28 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 233 (allA_succ_of_accept 26 27 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 233 (accept_3_2 25 27 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 233
  (Polychromatic418967fa.accept_17_6_10_12_1_4129 23 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 233 (accept_3_2 22 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 233 (accept_3_2 19 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 233 (accept_3_2 16 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 233 (accept_3_2 13 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 233 (Polychromatic418967fa.accept_18_12_9_17_1_7428 12 27 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 233 (accept_3_2 10 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 233 (accept_3_2 7 27 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 233 (accept_3_2 4 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 233 (accept_3_2 1 27 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 233))))))))))))))))))))))))))) (allB_succ 26 233 (allA_succ_of_accept 25 26 233 (accept_3_2
  25 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 233 (accept_3_2 22 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 233 (Polychromatic418967fa.accept_11_9_4_2_1_600
  20 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 233 (accept_3_2 19
  26 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 233 (accept_3_2 16 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 233
  (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 233 (accept_3_2 13 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 12 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 233 (accept_3_2 10 26 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 233 (accept_3_2 7 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  233 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 233 (accept_3_2 4 26 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 233 (Polychromatic418967fa.accept_18_2_8_17_1_4754
  2 26 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 233 (accept_3_2 1 26
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 233)))))))))))))))))))))))))) (allB_succ 25 233 (allA_of_3_0
  25 25 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 233 (allA_succ_of_accept 23 24 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 233 (accept_3_2 22 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 233 (accept_3_2 19 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 24 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 233
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 233 (accept_3_2 16 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 233 (accept_3_2 13 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 233 (accept_3_2 10 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 233 (accept_3_2 7 24 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 233 (accept_3_2 4 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 24 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 233 (accept_3_2 1 24 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 233)))))))))))))))))))))))) (allB_succ 23 233 (allA_succ_of_accept 22 23 233 (accept_3_2 22
  23 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 233
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 233 (accept_3_2 19 23 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 233
  (Polychromatic418967fa.accept_25_17_23_8_1_13888 17 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 23 233 (accept_3_2 16 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 23 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 233 (accept_3_2 13 23 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 233 (accept_3_2 10 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 23 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 233 (accept_3_2 7 23 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 233
  (Polychromatic418967fa.accept_24_5_23_17_1_13887 5 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 233 (accept_3_2 4 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 233 (accept_3_2 1 23 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 233))))))))))))))))))))))) (allB_succ 22 233 (allA_of_3_0 22 22 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 233 (allA_succ_of_accept 20 21 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 233 (accept_3_2 19 21 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  18 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 233
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 233 (accept_3_2 16 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 233 (accept_3_2 13 21 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 233 (accept_3_2 10 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 233 (accept_3_2 7 21 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 233 (accept_3_2 4 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 233 (accept_3_2 1 21 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 233))))))))))))))))))))) (allB_succ 20 233 (allA_succ_of_accept 19 20 233 (accept_3_2 19 20
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 233 (accept_3_2 16 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 233 (accept_3_2 13 20
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 233 (accept_3_2 10 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 233 (accept_3_2 7 20 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 233 (accept_3_2 4 20 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 233 (accept_3_2 1 20 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 233)))))))))))))))))))) (allB_succ 19 233 (allA_of_3_0 19 19 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 233 (allA_succ_of_accept 17 18 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 18 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 233 (accept_3_2 16 18 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 233
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 233 (accept_3_2 13 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 233 (accept_3_2 10 18 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 18 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 233
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 233 (accept_3_2 7 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 233 (accept_3_2 4 18 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043
  2 18 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 233 (accept_3_2 1 18
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 233)))))))))))))))))) (allB_succ 17 233 (allA_succ_of_accept
  16 17 233 (accept_3_2 16 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 17 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 233 (accept_3_2 13 17 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 233
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 233 (accept_3_2 10 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 233 (accept_3_2 7 17 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 233 (accept_3_2 4 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  233 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 17 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 233 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 17 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 233 (accept_3_2 1 17 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 233))))))))))))))))) (allB_succ 16 233 (allA_of_3_0 16 16 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 233 (allA_succ_of_accept 14 15 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 233 (accept_3_2 13 15 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12
  15 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 233 (accept_3_2 10 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 233 (accept_3_2 7 15 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 233 (accept_3_2 4 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 233 (accept_3_2 1 15 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 233))))))))))))))) (allB_succ 14 233 (allA_succ_of_accept 13 14 233 (accept_3_2 13 14 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  14 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 233 (accept_3_2 10 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 233 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 14 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 233 (accept_3_2 7 14 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 233
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 233 (accept_3_2 4 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 233 (accept_3_2 1 14 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 233)))))))))))))) (allB_succ 13 233 (allA_of_3_0 13 13 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 233 (allA_succ_of_accept 11 12 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 233 (accept_3_2 10 12 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 233 (Polychromatic418967fa.accept_18_9_12_17_1_6060
  9 12 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 233
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 12 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 233 (accept_3_2 7 12 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 12 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 233 (accept_3_2 4 12 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  12 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 233 (accept_3_2 1 12 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 233)))))))))))) (allB_succ 11 233 (allA_succ_of_accept 10 11 233
  (accept_3_2 10 11 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 233
  (Polychromatic418967fa.accept_21_9_11_2_1_238 9 11 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 11 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 233 (accept_3_2 7 11 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 233 (accept_3_2 4 11 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  11 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 233 (accept_3_2 1 11 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  233))))))))))) (allB_succ 10 233 (allA_of_3_0 10 10 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 233
  (allA_succ_of_accept 8 9 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 233 (accept_3_2 7 9 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 9 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 233 (Polychromatic418967fa.accept_17_5_9_12_1_9156 5
  9 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 233 (accept_3_2 4 9 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 233 (accept_3_2 1 9 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 233)))))))))
  (allB_succ 8 233 (allA_succ_of_accept 7 8 233 (accept_3_2 7 8 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 8 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 233 (accept_3_2 4 8 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 8 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 233 (accept_3_2 1 8 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 233))))))))
  (allB_succ 7 233 (allA_of_3_0 7 7 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 233 (allA_succ_of_accept 5
  6 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 233 (accept_3_2 4 6 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 233 (accept_3_2 1 6 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 233)))))) (allB_succ 5 233 (allA_succ_of_accept 4 5 233 (accept_3_2 4 5 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 233 (accept_3_2 1 5 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 233)))))
  (allB_succ 4 233 (allA_of_3_0 4 4 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 233 (allA_succ_of_accept 2
  3 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 233 (accept_3_2 1 3 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 233)))
  (allB_succ 2 233 (allA_succ_of_accept 1 2 233 (accept_3_2 1 2 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  233)) (allB_two
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


