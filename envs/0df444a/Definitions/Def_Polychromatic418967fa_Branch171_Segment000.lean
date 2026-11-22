-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch171_Segment000
-- name    : Polychromatic418967fa_Branch171_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:27:39.035629+00:00
-- url     : https://prove2.me/theorems/719dda08-2ee8-4140-8ed1-ee2c13661f0a
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

def Polychromatic418967fa.branch_171_segment_000 : allB 102 171 :=
  allB_succ' 71 101 171 (Eq.refl Bool.true) (allA_succ_of_accept 70 101 171 (accept_3_4 70 101 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 171 (accept_3_4 67 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 171 (Polychromatic418967fa.accept_15_5_11_6_1_692 65 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 171 (accept_3_4 64 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 171 (accept_3_4 61 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 171 (accept_3_4 58 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 171 (accept_3_4 55 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 171 (Polychromatic418967fa.accept_17_2_16_1_1_2260 53 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 171 (accept_3_4 52 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 171 (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 171 (accept_3_4 49 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 47 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 171 (accept_3_4 46 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 171 (accept_3_4 43 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 171 (Polychromatic418967fa.accept_16_9_5_11_1_3776 41 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 171 (accept_3_4 40 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 171 (accept_3_4 37 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 171 (Polychromatic418967fa.accept_17_2_16_1_1_2260 36 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 171 (Polychromatic418967fa.accept_15_5_11_6_1_692 35 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 171 (accept_3_4 34 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 171 (accept_3_4 31 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 171 (accept_3_4 28 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 171 (Polychromatic418967fa.accept_20_7_1_11_1_3766 27 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 171 (accept_3_4 25 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 171 (Polychromatic418967fa.accept_16_7_5_11_1_4777 23 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 171 (accept_3_4 22 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 171 (accept_3_4 19 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 171 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 171 (accept_3_4 16 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 101
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 171 (accept_3_4 13 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 171 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 171 (accept_3_4 10 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 101 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 171 (accept_3_4 7 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 171 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 101 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 171 (accept_3_4 4 101 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 101 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 171 (accept_3_4 1 101 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 100 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 100 171 (accept_3_5 71 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 100 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 70 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 100 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 171 (accept_3_5 68 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 100 171 (accept_3_5 65 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 100 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 171 (accept_3_5 62 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 171
  (Polychromatic418967fa.accept_11_5_1_6_1_774 60 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 100 171 (accept_3_5 59 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 100 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 58 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 171 (accept_3_5 56 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 171 (accept_3_5 53 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 171 (Polychromatic418967fa.accept_21_10_16_3_1_8047 52 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 171 (accept_3_5 50 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 171 (accept_3_5 47 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167 46 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 100 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 171 (accept_3_5 44 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 100 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 171 (accept_3_5 41 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 171 (accept_3_5 38 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 100 171 (accept_3_5 35 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 100 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 171 (accept_3_5 32 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 171 (accept_3_5 29 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 171 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 171 (accept_3_5 26 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 171
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 171 (accept_3_5 23 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 171 (Polychromatic418967fa.accept_22_21_12_17_1_9679 21 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 171 (accept_3_5 20 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 171 (accept_3_5 17 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 171 (accept_3_5 14 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 171 (accept_3_5 11 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 171 (Polychromatic418967fa.accept_21_10_16_3_1_8047 10 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 171 (Polychromatic418967fa.accept_16_9_4_11_1_2661 9 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 171 (accept_3_5 8 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 171 (accept_3_5 5 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 171 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 100 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 171 (accept_3_5 2 100 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 99 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 99 171 9 8 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 99 171 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 171 (Polychromatic418967fa.accept_16_6_3_11_1_3751 70 99
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 171 3 23 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 171 3 22 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 65
  99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 171
  (Polychromatic418967fa.accept_15_4_9_6_1_627 64 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 99 171 9 7 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 99 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 62 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 171 3 20 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 171
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 171 3 19 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  56 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 55 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 99 171 9 6 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 99 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 171 3 17 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 171
  (Polychromatic418967fa.accept_20_10_19_11_1_2384 50 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 99 171 (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 99 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 171 3 16 33 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 171 9 5 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 171
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 43 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 171 3 14 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 171 3 13 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 171
  (Polychromatic418967fa.accept_10_8_9_1_1_189 38 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 171 9 4 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 171
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 171 3 11 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 171 3 10 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 171
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 171 9 3 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 171 3 8 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 171 3 7 33 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 171
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 171 9 2 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 171 (Polychromatic418967fa.accept_21_17_15_3_1_4937 17 99
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 171 3 5 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 171 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 171 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 99
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 171 3 4 33 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 171 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 171 9 1 11 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 171
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 171 3 2 33 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 171 3 1 33 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 99 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 99 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 98 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 73 98 171 (accept_3_4 73 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 171 (Polychromatic418967fa.accept_21_9_14_3_1_9678 72 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 171 (accept_3_4 70 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 171
  (Polychromatic418967fa.accept_20_8_18_11_1_5133 68 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 171 (accept_3_4 67 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 171 (accept_3_4 64 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 62 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 171 (accept_3_4 61 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 171 (accept_3_4 58 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 171
  (Polychromatic418967fa.accept_20_16_18_11_1_9605 56 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 98 171 (accept_3_4 55 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 171 (accept_3_4 52 98 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 171 (Polychromatic418967fa.accept_21_9_14_3_1_9678
  51 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 171
  (Polychromatic418967fa.accept_21_8_14_3_1_9602 50 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 171 (accept_3_4 49 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 171 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 171 (accept_3_4 46 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 171
  (Polychromatic418967fa.accept_13_5_7_2_1_852 44 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 171 (accept_3_4 43 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 171 (accept_3_4 40 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 171 (accept_3_4 37 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 171 (Polychromatic418967fa.accept_17_2_13_1_1_3355 36 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 171 (accept_3_4 34 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 171 (accept_3_4 31 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 171 (accept_3_4 28 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 171
  (Polychromatic418967fa.accept_22_4_10_17_1_3182 26 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 171 (accept_3_4 25 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 171 (Polychromatic418967fa.accept_18_6_8_9_1_1960 24 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 171 (accept_3_4 22 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 171
  (Polychromatic418967fa.accept_22_20_10_17_1_9639 20 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 98 171 (accept_3_4 19 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 171 (accept_3_4 16 98 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 171
  (Polychromatic418967fa.accept_21_15_14_3_1_9677 15 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 98 171 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 98 171 (accept_3_4 13 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 98 171 (Polychromatic418967fa.accept_17_12_13_1_1_4478 12 98 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 98 171 (accept_3_4 10 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 98 171 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 171 (accept_3_4 7 98 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 98 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 98 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 171 (accept_3_4 4 98 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3
  98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 171 (accept_3_4 1 98 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 97 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 97 171 (accept_3_5 74 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 97 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 73 97 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 171 (accept_3_5 71 97 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 70
  97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 69 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 171 (accept_3_5 68 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 171 (accept_3_5 65 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 171
  (Polychromatic418967fa.accept_16_15_1_11_1_3747 63 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 171 (accept_3_5 62 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 171 (accept_3_5 59 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 171 (accept_3_5 56 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 171 (Polychromatic418967fa.accept_22_11_9_17_1_9599 55 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 171 (accept_3_5 53 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 171 (accept_3_5 50 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 171 (accept_3_5 47 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 171 (accept_3_5 44 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 171 (accept_3_5 41 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 171 (accept_3_5 38 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 171 (accept_3_5 35 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 171 (accept_3_5 32 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 171 (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 171 (accept_3_5 29 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 171
  (Polychromatic418967fa.accept_13_1_6_2_1_377 27 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 171 (accept_3_5 26 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 171 (accept_3_5 23 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 171 (accept_3_5 20 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 171 (Polychromatic418967fa.accept_24_19_1_3_1_9676 19 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 171 (accept_3_5 17 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 171
  (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 171 (accept_3_5 14 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 171 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 171 (accept_3_5 11 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 171 (accept_3_5 8 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  171 (Polychromatic418967fa.accept_23_7_5_10_1_9675 7 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 171 (accept_3_5 5 97 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 3 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 171 (accept_3_5 2 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  171 (Polychromatic418967fa.accept_13_1_6_2_1_377 1 97 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 96 171
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 96 171 3 25 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 96 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 74 96 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 171
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 73 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 171 3 24 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 171 (Polychromatic418967fa.accept_21_7_12_3_1_4849 70 96
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 171 3 23 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 171
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 96 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 67 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 171 3 22 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 65
  96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 96 171 3 21 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 96 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 171 3 20 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 171
  (Polychromatic418967fa.accept_13_7_5_2_1_401 59 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 171 3 19 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 171 (Polychromatic418967fa.accept_13_4_5_2_1_1436
  56 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 171
  (Polychromatic418967fa.accept_10_5_6_1_1_836 55 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 171 3 18 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 171 (Polychromatic418967fa.accept_21_11_12_3_1_6461 53 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 171 3 17 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 171 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 171 3 16 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 47
  96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 171
  (Polychromatic418967fa.accept_13_7_5_2_1_401 46 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 96 171 3 15 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 96 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 171 3 14 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 171
  (Polychromatic418967fa.accept_17_7_11_1_1_4503 41 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 171 (Polychromatic418967fa.accept_23_17_4_10_1_9674 40 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 171 3 13 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173
  38 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 171 3 12 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 171 (Polychromatic418967fa.accept_21_13_12_3_1_8028 34 96
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 171 3 11 32 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 171 (Polychromatic418967fa.accept_18_13_6_9_1_4280 31 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 171 3 10 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 171
  (Polychromatic418967fa.accept_21_7_12_3_1_4849 28 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 96 171 3 9 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 96 171 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 171 3 8 32 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 171 3 7 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 171 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 171
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 171 3 6 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 171 3 5 32 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 171
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 171 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 171 3 4 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 171 (Polychromatic418967fa.accept_21_11_12_3_1_6461 11 96
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 171
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 96 171 3 3 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 171 3 2 32 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 171
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 171 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4 96 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 171 3 1 32 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 95 171
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 95 171 19 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 95 171 (Polychromatic418967fa.accept_17_7_10_1_1_4488 75 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 95 171 (accept_3_4 73 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  95 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 72 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 95 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 171 (accept_3_4 70 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 171 (accept_3_4 67 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 66 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 95 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 65 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 171 (accept_3_4 64 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 95
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 171 (accept_3_4 61 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  95 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 95 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 171 (accept_3_4 58 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 57 95 171 19 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 95 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 171 (accept_3_4 55 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 171
  (Polychromatic418967fa.accept_20_13_15_11_1_6610 53 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 95 171 (accept_3_4 52 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 95 171 (Polychromatic418967fa.accept_13_12_4_2_1_2955 51 95 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 171 (accept_3_4 49 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 48
  95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 171
  (Polychromatic418967fa.accept_27_20_14_9_1_9673 47 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 171 (accept_3_4 46 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 171 (accept_3_4 43 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 171 (accept_3_4 40 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 95 171 19 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 95 171 (accept_3_4 37 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 95 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 171 (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 95
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 171 (accept_3_4 34 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 171 (Polychromatic418967fa.accept_12_9_11_3_1_772
  33 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 171 (accept_3_4 31 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 171 (Polychromatic418967fa.accept_18_12_5_9_1_6896 30 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 171 (accept_3_4 28 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 171 (accept_3_4 25 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 171 (accept_3_4 22 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 95 171 19 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 95 171 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 95 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 17 95
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 171 (accept_3_4 16 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 171 (accept_3_4 13 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 171 (accept_3_4 10 95 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 171 (accept_3_4 7 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 95 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 171 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 95 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 171 (accept_3_4 4 95 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 95 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 171 (accept_3_4 1 95 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 94 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 171 (accept_3_5 77 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 94 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 76 94 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 94 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 171 (accept_3_5 74 94 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 171
  (Polychromatic418967fa.accept_21_9_10_3_1_262 72 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 94 171 (accept_3_5 71 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  94 171 (Polychromatic418967fa.accept_13_5_3_2_1_1499 70 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 171 (accept_3_5 68 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 171 (accept_3_5 65 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 171 (Polychromatic418967fa.accept_13_12_3_2_1_1470 64 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 171 (accept_3_5 62 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 171
  (Polychromatic418967fa.accept_21_18_10_3_1_9672 60 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 171 (accept_3_5 59 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 58 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 171 (accept_3_5 56 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 171 (accept_3_5 53 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 171 (Polychromatic418967fa.accept_22_8_6_17_1_9593 52 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 171 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 171 (accept_3_5 50 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 171
  (Polychromatic418967fa.accept_13_9_3_2_1_399 48 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 171 (accept_3_5 47 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 171 (Polychromatic418967fa.accept_20_6_14_11_1_6537 46 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 171 (accept_3_5 44 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 171 (accept_3_5 41 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 171 (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 171 (accept_3_5 38 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 171
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 171 (accept_3_5 35 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 171 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 171 (accept_3_5 32 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 171 (accept_3_5 29 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 171 (accept_3_5 26 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 171
  (Polychromatic418967fa.accept_13_11_3_2_1_863 24 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 171 (accept_3_5 23 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 171 (accept_3_5 20 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 171 (accept_3_5 17 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 171 (Polychromatic418967fa.accept_21_16_10_3_1_9671 16 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 171 (accept_3_5 14 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 171
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 171 (accept_3_5 11 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 171 (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 171 (accept_3_5 8 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 171 (accept_3_5 5 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  171 (Polychromatic418967fa.accept_22_4_6_17_1_9670 4 94 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 171 (Polychromatic418967fa.accept_16_3_14_11_1_2654 3 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 171 (accept_3_5 2 94 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 93 171 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 93 171 3 26 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 93 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 93 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 76
  93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 93 171 3 25 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 93 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 171 3 24 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 71
  93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 93 171 3 23 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 93 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 67 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 171 3 22 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 65 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 93 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 171 3 21 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 93 171 3 20 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 93 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 93 171 3 19 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 93 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 56 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 171 3 18 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 52 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 93 171 3 17 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 171 3 16 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 171 3 15 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 171 (Polychromatic418967fa.accept_18_8_3_9_1_4232
  44 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 93 171 3 14 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 93 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 171 3 13 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 171 3 12 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 171 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 93 171 3 11 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 93 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 171 3 10 31 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 171 3 9 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 93 171 3 8 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 93 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 171 3 7 31 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 171 3 6 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 171
  (Polychromatic418967fa.accept_15_1_3_6_1_621 16 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 171 3 5 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 171 3 4 31 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 171 3 3 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 171 3 2 31 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 171 (Polychromatic418967fa.accept_17_4_8_1_1_5740 4 93 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 171 3 1 31 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 92 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 92 171 (accept_3_4 79 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 92 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 92 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 171 (accept_3_4 76 92 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 171 (accept_3_4 73 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 171 (accept_3_4 70 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 171 (accept_3_4 67 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 171 (accept_3_4 64 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 171
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 62 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 171 (accept_3_4 61 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 171 (accept_3_4 58 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 171 (accept_3_4 55 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 171 (accept_3_4 52 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 171
  (Polychromatic418967fa.accept_22_6_4_17_1_9627 50 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 171 (accept_3_4 49 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 171 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 171 (accept_3_4 46 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 171 (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 171 (accept_3_4 43 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 171 (accept_3_4 40 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 171
  (Polychromatic418967fa.accept_13_12_1_2_1_845 38 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 171 (accept_3_4 37 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 171 (accept_3_4 34 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 171 (accept_3_4 31 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 171 (accept_3_4 28 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 171 (accept_3_4 25 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 171 (accept_3_4 22 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 171 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 171
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 171 (accept_3_4 19 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 171 (accept_3_4 16 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 171
  (Polychromatic418967fa.accept_21_14_8_3_1_8085 14 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 171 (accept_3_4 13 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 171 (accept_3_4 10 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 171
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 171 (accept_3_4 7 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 171 (accept_3_4 4 92 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 92 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 171 (accept_3_4 1 92 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 91 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 80 91 171 (accept_3_5 80 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 91 171 (Polychromatic418967fa.accept_21_16_7_3_1_8093 79 91 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 78 91 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 171 (accept_3_5 77 91 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 76
  91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 171
  (Polychromatic418967fa.accept_11_9_3_6_1_797 75 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 171 (accept_3_5 74 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 171 (Polychromatic418967fa.accept_17_5_6_1_1_5735 73 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 171 (Polychromatic418967fa.accept_21_9_7_3_1_4888 72 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 171 (accept_3_5 71 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 171 (accept_3_5 68 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 67 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 171 (Polychromatic418967fa.accept_14_10_7_3_1_1022 66 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 171 (accept_3_5 65 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 171 (accept_3_5 62 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 171 (Polychromatic418967fa.accept_27_7_10_9_1_9669 61 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 171 (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 171 (accept_3_5 59 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 171 (accept_3_5 56 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 171 (Polychromatic418967fa.accept_15_10_1_6_1_3033 55 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 171 (Polychromatic418967fa.accept_15_9_1_6_1_657 54 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 171 (accept_3_5 53 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 171
  (Polychromatic418967fa.accept_21_9_7_3_1_4888 51 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 171 (accept_3_5 50 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 171 (Polychromatic418967fa.accept_22_5_3_17_1_9592 49 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 48 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 171 (accept_3_5 47 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 171 (accept_3_5 44 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 171 (Polychromatic418967fa.accept_21_1_7_3_1_6450 43 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 171 (accept_3_5 41 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 171
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 171 (accept_3_5 38 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 171 (Polychromatic418967fa.accept_15_7_1_6_1_6150 37 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 171 (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 171 (accept_3_5 35 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 171 (accept_3_5 32 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 171 (accept_3_5 29 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 171
  (Polychromatic418967fa.accept_21_6_7_3_1_8073 27 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 171 (accept_3_5 26 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 171 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 171 (accept_3_5 23 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 171 (accept_3_5 20 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 171 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 171 (accept_3_5 17 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 171
  (Polychromatic418967fa.accept_21_15_7_3_1_4886 15 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 171 (accept_3_5 14 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 171 (Polychromatic418967fa.accept_23_13_22_10_1_9668 13 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 171 (Polychromatic418967fa.accept_17_12_6_1_1_4517 12 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 171 (accept_3_5 11 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 171
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 171 (accept_3_5 8 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  171 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 171 (Polychromatic418967fa.accept_18_6_1_9_1_5551 6 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 171 (accept_3_5 5 91 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 171
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 171 (accept_3_5 2 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  171 (Polychromatic418967fa.accept_21_1_7_3_1_6450 1 91 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 90 171 (Eq.refl Bool.true) (allA_succ_of_gcd 81 90 171 9 9 10 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 90 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 90 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 171 3 26 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 76 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 90 171 3 25 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 90 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 171 9 8 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 171
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 171 3 23 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 68
  90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 171 3 22 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 171 9 7 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 171 3 20 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 59
  90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 90 171 3 19 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 90 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 55 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 171 9 6 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 171 3 17 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 50
  90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 171 3 16 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 171 (Polychromatic418967fa.accept_16_15_10_11_1_1727 47 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 171 9 5 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 171 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 171 3 14 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 90 171 3 13 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 90 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 171 9 4 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 171
  (Polychromatic418967fa.accept_20_15_10_11_1_8145 35 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 90 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 90 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 171 3 11 30 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 171 (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 171 3 10 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 171 9 3 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 171 3 8 30 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 171 3 7 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 171
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 171 9 2 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 171 3 5 30 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 171 3 4 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 171 9 1 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 171 (Polychromatic418967fa.accept_20_7_10_11_1_9577 7 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 171 3 2 30 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 171 3 1 30 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 89
  171 (Eq.refl Bool.true) (allA_succ_of_accept 82 89 171 (accept_3_4 82 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 89 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 89 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 171 (accept_3_4 79 89 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 171
  (Polychromatic418967fa.accept_25_2_14_21_1_9667 77 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 171 (accept_3_4 76 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 171 (accept_3_4 73 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 171 (accept_3_4 70 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 171 (accept_3_4 67 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 171 (accept_3_4 64 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 171 (Polychromatic418967fa.accept_25_13_14_21_1_9666 63 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 171 (accept_3_4 61 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 60 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 171
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 59 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 171 (accept_3_4 58 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 171 (accept_3_4 55 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 171
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 53 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 171 (accept_3_4 52 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 171 (accept_3_4 49 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 171
  (Polychromatic418967fa.accept_23_1_20_10_1_9665 47 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 171 (accept_3_4 46 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 171 (accept_3_4 43 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 171
  (Polychromatic418967fa.accept_27_14_8_9_1_9614 41 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 171 (accept_3_4 40 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 171 (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 171 (accept_3_4 37 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 171 (accept_3_4 34 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 171 (accept_3_4 31 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 171 (accept_3_4 28 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 171 (accept_3_4 25 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 171 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 171 (accept_3_4 22 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 171 (accept_3_4 19 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 171
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 171 (accept_3_4 16 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 171 (accept_3_4 13 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 89 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 171
  (Polychromatic418967fa.accept_23_11_20_10_1_9664 11 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 89 171 (accept_3_4 10 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 89 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 171 (accept_3_4 7 89 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 171 (accept_3_4 4 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 89 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 171 (accept_3_4 1 89 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 88 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 88 171 (accept_3_5 83 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 88 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 82 88 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 81 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 171 (accept_3_5 80 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 79
  88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 171 (accept_3_5 77 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 171 (Polychromatic418967fa.accept_21_12_4_3_1_4924 75 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 171 (accept_3_5 74 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 171
  (Polychromatic418967fa.accept_23_3_19_10_1_9663 72 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 171 (accept_3_5 71 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 171 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 171 (accept_3_5 68 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 171 (accept_3_5 65 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 171 (accept_3_5 62 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 171
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 171 (accept_3_5 59 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 171 (Polychromatic418967fa.accept_13_6_10_2_1_1449 58 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 171 (accept_3_5 56 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 171 (accept_3_5 53 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 52 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 171 (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 171 (accept_3_5 50 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 171 (accept_3_5 47 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 171 (Polychromatic418967fa.accept_27_19_7_9_1_9662 46 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 171 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 171 (accept_3_5 44 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 171 (accept_3_5 41 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 171 (Polychromatic418967fa.accept_17_6_3_1_1_7011 40 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 171 (accept_3_5 38 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 171 (accept_3_5 35 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 171 (accept_3_5 32 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 171 (accept_3_5 29 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 171 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 171 (accept_3_5 26 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 171
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 171 (accept_3_5 23 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 171 (accept_3_5 20 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 171 (accept_3_5 17 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 171 (accept_3_5 14 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 171
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 171 (accept_3_5 11 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 171 (Polychromatic418967fa.accept_24_10_16_3_1_9661 10 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 171 (accept_3_5 8 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 171 (accept_3_5 5 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  171 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 88 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 171 (accept_3_5 2 88 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 87 171 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 87 171 3 28 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 87 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 87 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 171 (Polychromatic418967fa.accept_11_5_10_6_1_793
  82 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 171 3 27 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 171
  (Polychromatic418967fa.accept_15_5_12_6_1_639 80 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 79 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 87 171 3 26 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 87 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063
  77 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 76 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 87 171 3 25 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 87 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 74 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 171 (Polychromatic418967fa.accept_22_7_21_17_1_9660 73 87
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 171 3 24 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 71 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 70 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 87 171 3 23 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 87 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 68
  87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 87 171 3 22 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 87 171 (Polychromatic418967fa.accept_15_5_12_6_1_639 65 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 171 3 21 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 62 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 171 (Polychromatic418967fa.accept_20_1_7_11_1_3673 61 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 87 171 3 20 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 87 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167
  59 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 171
  (Polychromatic418967fa.accept_13_6_9_2_1_838 58 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 87 171 3 19 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 87 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 171 3 18 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 171
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 171 3 17 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969
  50 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 171 3 16 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 47 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 171 3 15 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 171 (Polychromatic418967fa.accept_27_16_6_9_1_9659 43 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 171 3 14 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 171 (Polychromatic418967fa.accept_18_5_15_9_1_1919
  41 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 171
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 171 3 13 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 37 87
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 171 3 12 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 171
  (Polychromatic418967fa.accept_15_5_12_6_1_639 35 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 171 3 11 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 32
  87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 171
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 171 3 10 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 171 3 9 29 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 171
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 171 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 171 3 8 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 171 (Polychromatic418967fa.accept_17_6_2_1_1_3350 23 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 171 3 7 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 171 3 6 29 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 171 3 5 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 171
  (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 171 3 4 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 171 (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 87
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 171 3 3 29 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 171
  (Polychromatic418967fa.accept_23_8_18_10_1_9658 8 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 171 3 2 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 87 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 171 3 1 29 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 87 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 87 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 171
  (allA_succ_of_accept 85 86 171 (accept_3_4 85 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 171 (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 171 (accept_3_4 82 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 80 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 171 (accept_3_4 79 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 171 (accept_3_4 76 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 171
  (Polychromatic418967fa.accept_20_14_6_11_1_6600 74 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 171 (accept_3_4 73 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 171 (accept_3_4 70 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 171 (accept_3_4 67 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 171 (accept_3_4 64 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 63 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 171 (accept_3_4 61 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 171 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 171 (accept_3_4 58 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 171
  (Polychromatic418967fa.accept_20_16_6_11_1_9657 56 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 171 (accept_3_4 55 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 171 (accept_3_4 52 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 171 (Polychromatic418967fa.accept_16_3_6_11_1_2718 51 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 171 (accept_3_4 49 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 171 (accept_3_4 46 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 171
  (Polychromatic418967fa.accept_26_18_8_15_1_9656 44 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 171 (accept_3_4 43 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 171 (accept_3_4 40 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 171
  (Polychromatic418967fa.accept_21_17_2_3_1_4942 38 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 171 (accept_3_4 37 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 171 (accept_3_4 34 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 171 (accept_3_4 31 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 171 (accept_3_4 28 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 171 (accept_3_4 25 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 171 (accept_3_4 22 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 171 (accept_3_4 19 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 171 (accept_3_4 16 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 171 (accept_3_4 13 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 171 (accept_3_4 10 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 171 (accept_3_4 7 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 171 (accept_3_4 4 86 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 86 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  86 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 171 (accept_3_4 1 86 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 171
  (allA_succ_of_accept 84 85 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 171 (accept_3_5 83 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 81
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 171 (accept_3_5 80 85
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 171 (accept_3_5 77 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 171 (accept_3_5 74 85
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 171
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 73 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 171 (accept_3_5 71 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  69 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 171 (accept_3_5 68
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 171 (accept_3_5 65 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 171 (Polychromatic418967fa.accept_15_3_10_6_1_632
  63 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 171 (accept_3_5 62
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 85 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 171 (accept_3_5 59 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  57 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 171 (accept_3_5 56
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 171
  (Polychromatic418967fa.accept_16_7_5_11_1_4777 55 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 171 (accept_3_5 53 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 171 (accept_3_5 50 85
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 171 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 171 (accept_3_5 47 85 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  45 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 171 (accept_3_5 44
  85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 171
  (Polychromatic418967fa.accept_22_21_19_17_1_9655 43 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 171 (accept_3_5 41 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 171 (accept_3_5 38 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 171 (accept_3_5 35 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 171 (accept_3_5 32 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 171 (Polychromatic418967fa.accept_13_5_7_2_1_852 31 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 171 (accept_3_5 29 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 171
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 171 (accept_3_5 26 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 171 (accept_3_5 23 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 171 (accept_3_5 20 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 171 (accept_3_5 17 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 171
  (Polychromatic418967fa.accept_20_15_5_11_1_8096 15 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 171 (accept_3_5 14 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 171 (Polychromatic418967fa.accept_22_13_19_17_1_9654 13 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 171 (accept_3_5 11 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 171 (accept_3_5 8 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  171 (Polychromatic418967fa.accept_16_7_5_11_1_4777 7 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 171 (accept_3_5 5 85 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 171
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 171 (accept_3_5 2 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  171 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 85 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 84 171 (allA_succ_of_accept 83 84 171 (Polychromatic418967fa.accept_17_15_16_1_1_7080 83 84 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 171
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 82 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 84 171 3 27 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 84 171 (Polychromatic418967fa.accept_17_12_16_1_1_8363 80 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 171 3 26 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 171
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 76 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 171 3 25 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200
  74 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 171
  (Polychromatic418967fa.accept_13_8_6_2_1_865 73 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 171 3 24 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 84 171 (Polychromatic418967fa.accept_16_6_4_11_1_1719 70 84
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 171 3 23 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 171
  (Polychromatic418967fa.accept_27_14_3_9_1_9653 68 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 171 3 22 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 65
  84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 171
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 64 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 84 171 3 21 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 84 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 62 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 171 3 20 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 171
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 59 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 171 (Polychromatic418967fa.accept_18_4_12_9_1_2011 58 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 171 3 19 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 84 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 56
  84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 171 3 18 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 53 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 171 (Polychromatic418967fa.accept_18_16_12_9_1_5504 52 84
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 171 3 17 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 171
  (Polychromatic418967fa.accept_20_10_4_11_1_9652 50 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 171 3 16 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 47
  84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 171
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 46 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 84 171 3 15 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 84 171 (Polychromatic418967fa.accept_15_14_9_6_1_5093 44 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 171 3 14 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 171
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 40 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 171 3 13 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441
  38 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 171
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 171 3 12 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 171 3 11 28 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 171
  (Polychromatic418967fa.accept_17_15_16_1_1_7080 32 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 171 3 10 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 171 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  29 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 171
  (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 84 171 3 9 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 84 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 171 3 8 28 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 171 3 7 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 171 (Polychromatic418967fa.accept_22_20_18_17_1_9616 20 84
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 171
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 171 3 6 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 171 3 5 28 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 171
  (Polychromatic418967fa.accept_13_1_6_2_1_377 14 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 171 (Polychromatic418967fa.accept_20_13_4_11_1_9651 13 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 171 3 4 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 171
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 84 171 3 3 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 84 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 171 3 2 28 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 171
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 84 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 171 3 1 28 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 171 (Polychromatic418967fa.accept_17_2_16_1_1_2260 2 84 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 171
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 84 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 171
  (allA_succ_of_accept 82 83 171 (accept_3_4 82 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 171 (accept_3_4 79 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 171
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 171 (accept_3_4 76 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 171 (Polychromatic418967fa.accept_13_10_5_2_1_1477 75 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 171 (accept_3_4 73 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 171
  (Polychromatic418967fa.accept_16_7_3_11_1_3682 71 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 171 (accept_3_4 70 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 171 (accept_3_4 67 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 171 (Polychromatic418967fa.accept_14_10_13_3_1_2552 66 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 171 (accept_3_4 64 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 171 (Polychromatic418967fa.accept_16_15_3_11_1_5997 63 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 171 (accept_3_4 61 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 171
  (Polychromatic418967fa.accept_13_7_5_2_1_401 59 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 171 (accept_3_4 58 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 171 (accept_3_4 55 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 171 (Polychromatic418967fa.accept_16_6_3_11_1_3751 54 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 171 (accept_3_4 52 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 171 (accept_3_4 49 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 47 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 171 (accept_3_4 46 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 171 (accept_3_4 43 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 171
  (Polychromatic418967fa.accept_23_18_14_10_1_7900 41 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 83 171 (accept_3_4 40 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 83 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 171 (accept_3_4 37 83 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 171 (Polychromatic418967fa.accept_13_10_5_2_1_1477
  36 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 171
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 171 (accept_3_4 34 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 171 (accept_3_4 31 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 171
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 171 (accept_3_4 28 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 171 (Polychromatic418967fa.accept_21_6_20_3_1_9617 27 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 171 (accept_3_4 25 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 171 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 171 (accept_3_4 22 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 171 (accept_3_4 19 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 171
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 171 (accept_3_4 16 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 171 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 171 (accept_3_4 13 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 171 (accept_3_4 10 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 171 (accept_3_4 7 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 171 (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 83 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 171
  (Polychromatic418967fa.accept_27_5_2_9_1_9650 5 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 171 (accept_3_4 4 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 83 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 171 (accept_3_4 1 83 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 171
  (allA_succ_of_accept 81 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 171 (accept_3_5 80 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 78
  82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 171 (accept_3_5 77 82
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 76 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 171 (Polychromatic418967fa.accept_14_5_12_3_1_3397 75 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 171 (accept_3_5 74 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 72
  82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 171 (accept_3_5 71 82
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 171
  (Polychromatic418967fa.accept_13_5_4_2_1_846 70 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 171 (accept_3_5 68 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 171 (Polychromatic418967fa.accept_10_6_2_1_1_494
  66 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 171 (accept_3_5 65
  82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 171 (accept_3_5 62 82 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 171
  (Polychromatic418967fa.accept_21_18_19_3_1_9649 60 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 171 (accept_3_5 59 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 171 (accept_3_5 56 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 171 (accept_3_5 53 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 171 (Polychromatic418967fa.accept_25_2_7_21_1_9648 52 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 171 (accept_3_5 50 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 171
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 171 (accept_3_5 47 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 171 (accept_3_5 44 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 171 (accept_3_5 41 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 171 (Polychromatic418967fa.accept_22_18_16_17_1_8011 40 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 171 (accept_3_5 38 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 171 (accept_3_5 35 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 171 (accept_3_5 32 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 171 (accept_3_5 29 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 171 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 171 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 171 (accept_3_5 26 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 171
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 171 (accept_3_5 23 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 171 (accept_3_5 20 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 171 (accept_3_5 17 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 171 (accept_3_5 14 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 171 (accept_3_5 11 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 171 (accept_3_5 8 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 171 (accept_3_5 5 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  171 (Polychromatic418967fa.accept_17_4_14_1_1_1363 4 82 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 82 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 171 (accept_3_5 2 82 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 171
  (allA_succ_of_accept 80 81 171 (Polychromatic418967fa.accept_17_12_13_1_1_4478 80 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 171 3 26 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 171 3 25 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 171 9 8 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 171 3 23 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 171 3 22 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 65
  81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 171 9 7 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 171 3 20 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 171 3 19 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 171 (Polychromatic418967fa.accept_20_16_1_11_1_9647
  56 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 171 9 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 171 (Polychromatic418967fa.accept_20_12_1_11_1_5096 52 81
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 171 3 17 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 171 3 16 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 171 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 171 9 5 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 171 (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 171 3 14 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 171 3 13 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 171 9 4 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 171 3 11 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 171
  (Polychromatic418967fa.accept_20_12_1_11_1_5096 32 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 171 3 10 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 171
  (Polychromatic418967fa.accept_16_12_1_11_1_5958 28 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 171 9 3 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 171 3 8 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 171 3 7 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 171 9 2 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 171 (Polychromatic418967fa.accept_20_16_1_11_1_9647 16 81
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 171 3 5 27 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 171 3 4 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 171 9 1 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 171 3 2 27 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 171 (Polychromatic418967fa.accept_20_4_1_11_1_9646 4 81 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 171 3 1 27 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 171
  (allA_succ_of_accept 79 80 171 (accept_3_4 79 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 171 (accept_3_4 76 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 75 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 74 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 171 (accept_3_4 73 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 72 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 171 (accept_3_4 70 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 171 (Polychromatic418967fa.accept_14_13_10_3_1_1037 69 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 171
  (Polychromatic418967fa.accept_23_22_11_10_1_6063 68 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 80 171 (accept_3_4 67 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 80 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 80 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 171 (accept_3_4 64 80 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  63 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 171 (accept_3_4 61 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 171 (Polychromatic418967fa.accept_18_6_8_9_1_1960 60 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 171 (accept_3_4 58 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 171
  (Polychromatic418967fa.accept_15_11_5_6_1_669 56 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 171 (accept_3_4 55 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 171 (accept_3_4 52 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 171 (Polychromatic418967fa.accept_21_9_17_3_1_6408 51 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 171
  (Polychromatic418967fa.accept_17_16_12_1_1_5785 50 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 171 (accept_3_4 49 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 171 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 171 (accept_3_4 46 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 171 (Polychromatic418967fa.accept_23_22_11_10_1_6063 45 80 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 171
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 44 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 171 (accept_3_4 43 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 171 (accept_3_4 40 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 171 (Polychromatic418967fa.accept_18_3_8_9_1_1956 39 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 171
  (Polychromatic418967fa.accept_25_13_5_21_1_9645 38 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 171 (accept_3_4 37 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 171 (Polychromatic418967fa.accept_21_15_17_3_1_3373 36 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 171 (accept_3_4 34 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 171
  (Polychromatic418967fa.accept_17_15_12_1_1_3365 32 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 171 (accept_3_4 31 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 171 (accept_3_4 28 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 171 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 171
  (Polychromatic418967fa.accept_15_11_5_6_1_669 26 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 171 (accept_3_4 25 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 171 (Polychromatic418967fa.accept_18_6_8_9_1_1960 24 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 171 (accept_3_4 22 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 171 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 171
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 171 (accept_3_4 19 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 171 (accept_3_4 16 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 171 (Polychromatic418967fa.accept_17_15_12_1_1_3365 15 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 171
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 171 (accept_3_4 13 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 171 (accept_3_4 10 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 80 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 171 (accept_3_4 7 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 171 (accept_3_4 4 80 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 80 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 171 (Polychromatic418967fa.accept_21_2_17_3_1_9644
  2 80 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 171 (accept_3_4 1 80
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 171
  (allA_succ_of_accept 78 79 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 171 (accept_3_5 77 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 75
  79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 171 (accept_3_5 74 79
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 171
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 73 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 171 (accept_3_5 71 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 69
  79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 171 (accept_3_5 68 79
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 171
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 67 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 171 (Polychromatic418967fa.accept_26_14_1_15_1_9643 66 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 171 (accept_3_5 65 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 171
  (Polychromatic418967fa.accept_22_19_13_17_1_9642 63 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 79 171 (accept_3_5 62 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 79 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 171 (accept_3_5 59 79 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 58
  79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 171 (accept_3_5 56 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 171 (accept_3_5 53 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 171
  (Polychromatic418967fa.accept_13_12_1_2_1_845 51 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 171 (accept_3_5 50 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 49 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 171 (accept_3_5 47 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 171 (accept_3_5 44 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 171 (accept_3_5 41 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 171
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 171 (accept_3_5 38 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 171 (accept_3_5 35 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 171 (accept_3_5 32 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 171 (Polychromatic418967fa.accept_21_10_16_3_1_8047 31 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 171 (Polychromatic418967fa.accept_20_10_19_11_1_2384 30 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 171 (accept_3_5 29 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 171 (accept_3_5 26 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 171 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 171 (accept_3_5 23 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 171 (accept_3_5 20 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 171 (accept_3_5 17 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 171 (accept_3_5 14 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 171 (accept_3_5 11 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 171 (accept_3_5 8 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  171 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 171 (accept_3_5 5 79 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 171
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 171 (accept_3_5 2 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  171 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 171
  (allA_succ_of_accept 77 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 171 3 25 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 171 3 24 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 71
  78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 171 3 23 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 171 3 22 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 171 3 21 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  62 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 171 3 20 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 171 3 19 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 171 (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 171 3 18 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 171 3 17 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 171 3 16 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 171 3 15 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 171
  (Polychromatic418967fa.accept_10_3_8_1_1_182 43 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 171 3 14 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 171 3 13 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 171
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 171 3 12 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 171 (Polychromatic418967fa.accept_15_5_3_6_1_2128
  35 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 171 3 11 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 171 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 171 3 10 26 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 171 3 9 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 171 3 8 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 171 3 7 26 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 171 3 6 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 171 3 5 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 171 3 4 26 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 171 3 3 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 171 3 2 26 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 171 3 1 26 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 171
  (allA_succ_of_accept 76 77 171 (accept_3_4 76 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 75 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 171 (accept_3_4 73 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 72 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 171
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 171 (accept_3_4 70 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 171 (accept_3_4 67 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 171
  (Polychromatic418967fa.accept_20_5_17_11_1_6571 65 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 171 (accept_3_4 64 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 171 (Polychromatic418967fa.accept_28_7_21_3_1_9641 63 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 171 (accept_3_4 61 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 171 (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 171
  (Polychromatic418967fa.accept_17_8_9_1_1_3340 59 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 171 (accept_3_4 58 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 171 (accept_3_4 55 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 171
  (Polychromatic418967fa.accept_13_1_12_2_1_384 53 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 171 (accept_3_4 52 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 171 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 171 (accept_3_4 49 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 171 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 171
  (Polychromatic418967fa.accept_27_20_23_9_1_9594 47 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 171 (accept_3_4 46 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 171 (accept_3_4 43 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 171
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 41 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 171 (accept_3_4 40 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 171 (accept_3_4 37 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 171
  (Polychromatic418967fa.accept_22_13_11_17_1_9640 35 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 77 171 (accept_3_4 34 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 77 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 171 (accept_3_4 31 77 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 171
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 171 (accept_3_4 28 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 171 (accept_3_4 25 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 171
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 171 (accept_3_4 22 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 171 (accept_3_4 19 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 171
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 171 (accept_3_4 16 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 171 (Polychromatic418967fa.accept_17_15_9_1_1_3363 15 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 171 (accept_3_4 13 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 171
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 171 (accept_3_4 10 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 171 (accept_3_4 7 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 171
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 171 (accept_3_4 4 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  171 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 77 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 171 (accept_3_4 1 77 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 171 (allA_succ_of_accept 75 76 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 75 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 171 (accept_3_5 74 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 171 (accept_3_5 71 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 171 (Polychromatic418967fa.accept_15_10_1_6_1_3033 70 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 171 (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 171 (accept_3_5 68 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 171 (accept_3_5 65 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 171 (Polychromatic418967fa.accept_22_20_10_17_1_9639 64 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 171 (accept_3_5 62 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 171 (accept_3_5 59 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 76 171 19 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 76 171 (accept_3_5 56 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 171 (accept_3_5 53 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  52 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 171 (accept_3_5 50 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 171 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 171 (accept_3_5 47 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 171
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 171 (accept_3_5 44 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 171 (accept_3_5 41 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 171 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 171 19 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 76
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 171 (accept_3_5 35 76 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 171
  (Polychromatic418967fa.accept_36_34_4_27_1_9638 34 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 76 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 171 (accept_3_5 32 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 171 (accept_3_5 29 76
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 171
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 28 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 76 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 171 (accept_3_5 26 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055
  24 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 171 (accept_3_5 23
  76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 76 171 (Polychromatic418967fa.accept_17_4_8_1_1_5740 21 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 171 (accept_3_5 20 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 19 76 171 19 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 18 76 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 171 (accept_3_5 17 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 171 (accept_3_5 14 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 171 (accept_3_5 11 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 76 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 171 (accept_3_5 8 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 171 (accept_3_5 5 76 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422
  3 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 171 (accept_3_5 2 76
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 171 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 76 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 171 (allA_succ_of_accept
  74 75 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 74 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 73 75 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 171 3 24 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 171 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 171 3 23 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 171 (Polychromatic418967fa.accept_13_3_10_2_1_381
  68 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 171
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 67 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 171 3 22 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 171 3 21 25 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 171
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 62 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 171 (Polychromatic418967fa.accept_17_10_7_1_1_7024 61 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 171 3 20 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  59 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 171 3 19 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 55 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 171 3 18 25 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 171
  (Polychromatic418967fa.accept_20_13_15_11_1_6610 53 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 75 171 (Polychromatic418967fa.accept_21_10_12_3_1_8076 52 75 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 171 3 17 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 171 3 16 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 47
  75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 171
  (Polychromatic418967fa.accept_10_6_5_1_1_482 46 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 75 171 3 15 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 75 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 171 3 14 25 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 171
  (Polychromatic418967fa.accept_21_20_12_3_1_3387 41 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 171 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 171 3 13 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 171 (Polychromatic418967fa.accept_13_12_10_2_1_1451
  38 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 171 3 12 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 75 171 (Polychromatic418967fa.accept_21_14_12_3_1_9637 35 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 171 3 11 25 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 171
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 171 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 171 3 10 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 171
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 28 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 171 3 9 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 171 3 8 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 171 3 7 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 171 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 171 3 6 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 171 (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 171 3 5 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 171
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 171 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 171 3 4 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 75
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 171
  (Polychromatic418967fa.accept_17_10_7_1_1_7024 10 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 171 3 3 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 171 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 171 3 2 25 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 171
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 75 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 171 3 1 25 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 171
  (allA_succ_of_accept 73 74 171 (accept_3_4 73 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  74 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 171 (accept_3_4 70 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 171
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 68 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 171 (accept_3_4 67 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 171 (accept_3_4 64 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 171 (accept_3_4 61 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 171 (Polychromatic418967fa.accept_16_12_10_11_1_2667 60 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 171 (accept_3_4 58 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 171
  (Polychromatic418967fa.accept_17_5_6_1_1_5735 56 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 171 (accept_3_4 55 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 171 (accept_3_4 52 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 171 (Polychromatic418967fa.accept_34_17_6_1_1_9636 51 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 171 (accept_3_4 49 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 171 (accept_3_4 46 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 171
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 171 (accept_3_4 43 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 171 (accept_3_4 40 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 171 (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 171
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 38 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 171 (accept_3_4 37 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 171 (accept_3_4 34 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 171
  (Polychromatic418967fa.accept_13_6_9_2_1_838 32 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 171 (accept_3_4 31 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 171 (accept_3_4 28 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 171
  (Polychromatic418967fa.accept_20_6_14_11_1_6537 26 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 171 (accept_3_4 25 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 171 (accept_3_4 22 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 171 (accept_3_4 19 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 171 (accept_3_4 16 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 171
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 171 (accept_3_4 13 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 171 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 171 (accept_3_4 10 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 171 (accept_3_4 7 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 171 (accept_3_4 4 74 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 74 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 171 (Polychromatic418967fa.accept_17_2_6_1_1_8357 2
  74 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 171 (accept_3_4 1 74 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 171 (allA_succ_of_accept
  72 73 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 171 (accept_3_5 71 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 73 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 171 (accept_3_5 68 73 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 171 (Polychromatic418967fa.accept_11_1_7_6_1_378
  67 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 171 (accept_3_5 65 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 171 (Polychromatic418967fa.accept_20_3_13_11_1_9634 63 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 171 (accept_3_5 62 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 171 (Polychromatic418967fa.accept_25_11_23_21_1_9635 61 73
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 171
  (Polychromatic418967fa.accept_18_6_1_9_1_5551 60 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 171 (accept_3_5 59 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 171 (accept_3_5 56 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 171 (Polychromatic418967fa.accept_17_4_5_1_1_5776 55 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 171 (accept_3_5 53 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 171 (Polychromatic418967fa.accept_21_9_10_3_1_262 51 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 171 (accept_3_5 50 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 171 (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 171 (accept_3_5 47 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 171 (accept_3_5 44 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 171 (Polychromatic418967fa.accept_20_3_13_11_1_9634 43 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 171 (accept_3_5 41 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 171 (Polychromatic418967fa.accept_18_3_1_9_1_1929 39 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 171 (accept_3_5 38 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 37 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 171
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 171 (accept_3_5 35 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 171 (accept_3_5 32 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 171 (Polychromatic418967fa.accept_27_4_19_9_1_9633 31 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 171 (accept_3_5 29 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 171 (Polychromatic418967fa.accept_25_2_23_21_1_7793 27 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 171 (accept_3_5 26 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 171 (Polychromatic418967fa.accept_36_25_1_27_1_9632 25 73
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 171
  (Polychromatic418967fa.accept_18_6_1_9_1_5551 24 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 171 (accept_3_5 23 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 171 (accept_3_5 20 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 171 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 171 (accept_3_5 17 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 171 (Polychromatic418967fa.accept_20_15_13_11_1_5110 15 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 171 (accept_3_5 14 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 171 (Polychromatic418967fa.accept_21_13_10_3_1_1051 13 73
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 171 (accept_3_5 11 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 171 (accept_3_5 8 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 171 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 73 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 171 (accept_3_5 5 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 171 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3 73 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 171 (accept_3_5 2 73 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 73 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 171 (allA_succ_of_accept 71
  72 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 171 (Polychromatic418967fa.accept_13_5_7_2_1_852 70 72 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 171 3 23 24 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 171 3 22 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 171 (Polychromatic418967fa.accept_15_5_12_6_1_639
  65 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 171 9 7 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 171 3 20 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 171
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 171 (Polychromatic418967fa.accept_21_16_9_3_1_6436 58 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 171 3 19 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 56
  72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 171 9 6 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 72
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 171 3 17 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 171 3 16 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 171 9 5 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 171 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 171 3 14 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 171 3 13 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 171 (Polychromatic418967fa.accept_21_17_9_3_1_6437
  38 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 171 9 4 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 171 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 171 3 11 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 171 (Polychromatic418967fa.accept_13_5_7_2_1_852 31 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 171 3 10 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 171
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 171 9 3 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 171 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 72
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 171 3 8 24 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 171
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 171 3 7 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 171 9 2 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 171 3 5 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 171
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 14 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 171 3 4 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 171 (Polychromatic418967fa.accept_22_11_6_17_1_9631 11 72
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 171
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 171 9 1 8 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 171 3 2 24 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 171 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 72 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 171 3 1 24 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 72 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 171
  (allA_succ_of_accept 70 71 171 (accept_3_4 70 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 171 (accept_3_4 67 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 66 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 171 (accept_3_4 64 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 63 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 171 (accept_3_4 61 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 171
  (Polychromatic418967fa.accept_21_17_8_3_1_9576 59 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 171 (accept_3_4 58 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 171 (accept_3_4 55 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 171 (accept_3_4 52 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 171 (accept_3_4 49 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 171 (accept_3_4 46 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 171 (accept_3_4 43 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 171 (Polychromatic418967fa.accept_28_14_15_3_1_3400 42 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 171
  (Polychromatic418967fa.accept_22_19_5_17_1_9630 41 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 171 (accept_3_4 40 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 171 (accept_3_4 37 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 171
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 171 (accept_3_4 34 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 171 (accept_3_4 31 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 171
  (Polychromatic418967fa.accept_27_2_17_9_1_9629 29 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 171 (accept_3_4 28 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 171 (accept_3_4 25 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 171 (accept_3_4 22 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 171 (accept_3_4 19 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 171
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 171 (accept_3_4 16 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 171 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 171 (accept_3_4 13 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 171 (accept_3_4 10 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 171 (accept_3_4 7 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 171 (Polychromatic418967fa.accept_17_6_3_1_1_7011 6 71 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 171 (accept_3_4 4 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 71 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 171 (accept_3_4 1 71 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 171 (allA_succ_of_accept 69 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 171 (accept_3_5 68 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 70 171 (accept_3_5 65 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  70 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173 64 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 70 171 (Polychromatic418967fa.accept_15_3_10_6_1_632 63 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 171 (accept_3_5 62 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 171
  (Polychromatic418967fa.accept_23_14_1_10_1_9628 60 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 70 171 (accept_3_5 59 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  70 171 (Polychromatic418967fa.accept_21_16_7_3_1_8093 58 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 171 (accept_3_5 56 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 171 (accept_3_5 53 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 171 (Polychromatic418967fa.accept_16_4_6_11_1_3753 52 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 171 (accept_3_5 50 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 171
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 171 (accept_3_5 47 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 171 (accept_3_5 44 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 171 (accept_3_5 41 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 171 (Polychromatic418967fa.accept_17_6_2_1_1_3350 40 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 171 (Polychromatic418967fa.accept_20_19_10_11_1_5107 39 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 171 (accept_3_5 38 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 171
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 171 (accept_3_5 35 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 171 (Polychromatic418967fa.accept_15_4_10_6_1_2997 34 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 171 (accept_3_5 32 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 171 (accept_3_5 29 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 171 (Polychromatic418967fa.accept_22_6_4_17_1_9627 28 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 171 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 171 (accept_3_5 26 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 171 (accept_3_5 23 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 171 (accept_3_5 20 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 171 (accept_3_5 17 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 171 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 171 (accept_3_5 14 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 171
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 171 (accept_3_5 11 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 171 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 171 (accept_3_5 8 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 171 (accept_3_5 5 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  171 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4 70 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 171 (accept_3_5 2 70 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 171 (allA_succ_of_accept 68 69
  171 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 171 3 22 23 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 64 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 171 3 21 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 171 3 20 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 171 3 19 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 171
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 171 3 18 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 171
  (Polychromatic418967fa.accept_10_2_9_1_1_185 52 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 171 3 17 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 171 3 16 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 171 3 15 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 171 3 14 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 171 (Polychromatic418967fa.accept_16_8_5_11_1_4776 40 69
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 171 3 13 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 171 3 12 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 171 3 11 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 171 3 10 23 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 171 3 9 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 171 3 8 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 171 3 7 23 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 171
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 171 3 6 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 171 3 5 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 171 3 4 23 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 171 3 3 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 171 3 2 23 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 171 3 1 23 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 69 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 171 (allA_succ_of_accept 67 68 171 (accept_3_4 67 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 68 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 171 (accept_3_4 64 68 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 63
  68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 171
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 62 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 171 (accept_3_4 61 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 171 (Polychromatic418967fa.accept_16_12_4_11_1_3710 60 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 171 (accept_3_4 58 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 171
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 56 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 171 (accept_3_4 55 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 171 (accept_3_4 52 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 171 (accept_3_4 49 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 171 (accept_3_4 46 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 171 (Polychromatic418967fa.accept_22_1_2_17_1_6348 45 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 171 (accept_3_4 43 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 171 (accept_3_4 40 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 171
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 171 (accept_3_4 37 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 171 (accept_3_4 34 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 171 (accept_3_4 31 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 171 (accept_3_4 28 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 171
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 171 (accept_3_4 25 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 171 (accept_3_4 22 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 171 (Polychromatic418967fa.accept_18_3_14_9_1_4264 21 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 171
  (Polychromatic418967fa.accept_23_20_22_10_1_9626 20 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 68 171 (accept_3_4 19 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 68 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 171 (accept_3_4 16 68 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 171
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 171 (accept_3_4 13 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 171 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 171 (accept_3_4 10 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 171 (accept_3_4 7 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 68 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 171 (accept_3_4 4 68 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 68 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 171 (accept_3_4 1 68 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 171 (allA_succ_of_accept 66 67
  171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 66 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 171 (accept_3_5 65 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 171 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 67
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 171 (accept_3_5 62 67 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 171 (Polychromatic418967fa.accept_15_1_7_6_1_6127
  61 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 171
  (Polychromatic418967fa.accept_11_5_1_6_1_774 60 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 171 (accept_3_5 59 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 171 (accept_3_5 56 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 171
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 171 (accept_3_5 53 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 171 (accept_3_5 50 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 171 (accept_3_5 47 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 171 (accept_3_5 44 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 171 (accept_3_5 41 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 171 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 171 (accept_3_5 38 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 171 (Polychromatic418967fa.accept_41_37_26_7_1_9625 37 67
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 171 (accept_3_5 35 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 171 (accept_3_5 32 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 171 (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 171
  (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 171 (accept_3_5 29 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 171 (accept_3_5 26 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 171 (Polychromatic418967fa.accept_23_2_21_10_1_9588 25 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 171
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 171 (accept_3_5 23 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 171 (accept_3_5 20 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 171 (Polychromatic418967fa.accept_17_2_16_1_1_2260 19 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 171 (accept_3_5 17 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 171 (accept_3_5 14 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 171 (accept_3_5 11 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 171 (accept_3_5 8 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 67 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 171 (accept_3_5 5 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 171 (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 67 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 171 (accept_3_5 2 67 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 171 (allA_succ_of_accept 65 66
  171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 171 3 21 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  62 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 171 3 20 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 171 (Polychromatic418967fa.accept_18_5_12_9_1_6871 59 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 171 3 19 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 171 3 18 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 171 3 17 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 171 3 16 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 171
  (Polychromatic418967fa.accept_10_7_6_1_1_486 47 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 171 3 15 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 44
  66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 171
  (Polychromatic418967fa.accept_17_9_15_1_1_7048 43 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 171 3 14 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 171 3 13 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 171 3 12 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 35
  66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 171 3 11 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 171 (Polychromatic418967fa.accept_25_6_16_21_1_9624 31 66
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 171 3 10 22 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 171 3 9 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 171 3 8 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 171 (Polychromatic418967fa.accept_16_7_2_11_1_931 23 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 171 3 7 22 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 171 (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 171 3 6 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 171 3 5 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 171 3 4 22 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 171
  (Polychromatic418967fa.accept_18_11_12_9_1_992 11 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 171 3 3 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 171
  (Polychromatic418967fa.accept_10_7_6_1_1_486 7 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 171 3 2 22 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 66 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 171 3 1 22 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 66 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 171 (allA_succ_of_accept 64 65 171 (accept_3_4 64 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 63 65 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 171 (accept_3_4 61 65 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 171 (Polychromatic418967fa.accept_11_5_10_6_1_793
  60 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 171 (accept_3_4 58 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 171 (accept_3_4 55 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 171
  (Polychromatic418967fa.accept_27_26_11_9_1_9623 53 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 171 (accept_3_4 52 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 171 (Polychromatic418967fa.accept_18_15_11_9_1_4256 51 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 171 (accept_3_4 49 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 171 (accept_3_4 46 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 171 (accept_3_4 43 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 171 (accept_3_4 40 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 171 (accept_3_4 37 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 171
  (Polychromatic418967fa.accept_20_15_5_11_1_8096 35 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 171 (accept_3_4 34 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 171 (accept_3_4 31 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 171 (accept_3_4 28 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 171 (accept_3_4 25 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 171
  (Polychromatic418967fa.accept_22_1_21_17_1_9585 23 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 171 (accept_3_4 22 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 171 (accept_3_4 19 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 171
  (Polychromatic418967fa.accept_20_17_5_11_1_9622 17 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 171 (accept_3_4 16 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 171 (accept_3_4 13 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 171
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 171 (accept_3_4 10 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 171 (accept_3_4 7 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 171 (accept_3_4 4 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 65 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 65 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 171 (accept_3_4 1 65 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 65 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64
  171 (allA_succ_of_accept 63 64 171 (Polychromatic418967fa.accept_17_12_13_1_1_4478 63 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 171 (accept_3_5 62 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 64 171 (accept_3_5 59 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  64 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 64 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 171 (accept_3_5 56 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 64 171 (accept_3_5 53 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  64 171 (Polychromatic418967fa.accept_21_10_1_3_1_8092 52 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 64 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 171 (accept_3_5 50 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 171
  (Polychromatic418967fa.accept_17_14_13_1_1_3356 48 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 171 (accept_3_5 47 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 171 (accept_3_5 44 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 171 (accept_3_5 41 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 171 (accept_3_5 38 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 171 (accept_3_5 35 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 171 (Polychromatic418967fa.accept_22_12_20_17_1_9621 34 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 171 (accept_3_5 32 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 171 (accept_3_5 29 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 171 (accept_3_5 26 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 171
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 171 (accept_3_5 23 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 171 (Polychromatic418967fa.accept_27_22_10_9_1_9620 22 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 171 (Polychromatic418967fa.accept_20_1_4_11_1_5098 21 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 171 (accept_3_5 20 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 171 (accept_3_5 17 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 171 (accept_3_5 14 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 171 (accept_3_5 11 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 171 (accept_3_5 8 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 171 (accept_3_5 5 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 64 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 171 (accept_3_5 2 64 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 171 (allA_succ_of_accept 62 63 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 62 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 171 (Polychromatic418967fa.accept_13_9_11_2_1_1491 61 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 171 3 20 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 171 (Polychromatic418967fa.accept_25_9_13_21_1_9619
  59 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 171 3 19 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 171 (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 63
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 171 9 6 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 171
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 171 3 17 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 171 (Polychromatic418967fa.accept_15_5_3_6_1_2128
  50 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 171
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 171 3 16 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 171 (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 63 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 171 9 5 7 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 171 (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 171 3 14 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  41 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 171
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 171 3 13 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 171 (Polychromatic418967fa.accept_25_12_13_21_1_9618 37 63
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 171 9 4 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 171
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 171 (Polychromatic418967fa.accept_20_14_3_11_1_6541 34 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 171 3 11 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 32
  63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 171
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 171 3 10 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 63 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 171 9 3 7 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 171
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 171 3 8 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 63
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 22 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 171 3 7 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 171 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 63
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 171 9 2 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 171
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 171 3 5 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 63 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 171
  (Polychromatic418967fa.accept_17_13_12_1_1_4524 13 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 171 3 4 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 63
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 171 9 1 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 171 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 171 3 2 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 171 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 63 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 171 3 1 21 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 63 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 171 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 63 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 171 (allA_succ_of_accept 61 62 171
  (accept_3_4 61 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 171 (accept_3_4 58 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 171 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 171 (accept_3_4 55
  62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 171
  (Polychromatic418967fa.accept_12_6_2_3_1_354 54 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 171 (accept_3_4 52 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 171
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 171 (accept_3_4 49 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 171 (Polychromatic418967fa.accept_21_6_20_3_1_9617 48 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 171 (accept_3_4 46 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 171 (accept_3_4 43 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 171 (accept_3_4 40 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 171
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 171 (accept_3_4 37 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 171 (accept_3_4 34 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 171 (accept_3_4 31 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 171 (accept_3_4 28 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 62 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 171 (accept_3_4 25 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 171 (accept_3_4 22 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 171
  (Polychromatic418967fa.accept_22_20_18_17_1_9616 20 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 62 171 (accept_3_4 19 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 62 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 171 (accept_3_4 16 62 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 171
  (Polychromatic418967fa.accept_24_15_14_3_1_9615 15 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 62 171 (Polychromatic418967fa.accept_27_14_8_9_1_9614 14 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 171 (accept_3_4 13 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 62 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 171 (accept_3_4 10 62
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 171
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 171 (accept_3_4 7 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 171 (accept_3_4 4 62 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 62 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  62 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 171 (accept_3_4 1 62 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 171 (allA_succ_of_accept 60 61 171
  (Polychromatic418967fa.accept_17_9_10_1_1_3345 60 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 171 (accept_3_5 59 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 171 (accept_3_5 56 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 171 (accept_3_5 53 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 171 (accept_3_5 50 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 171 (Polychromatic418967fa.accept_25_24_11_21_1_9613 49 61 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 171
  (Polychromatic418967fa.accept_15_3_1_6_1_206 48 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 171 (accept_3_5 47 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 171 (accept_3_5 44 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 171 (accept_3_5 41 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 171 (Polychromatic418967fa.accept_15_9_1_6_1_657 39 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 171 (accept_3_5 38 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 171 (accept_3_5 35 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 171 (accept_3_5 32 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 171 (accept_3_5 29 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 171 (accept_3_5 26 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 171 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 171
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 171 (accept_3_5 23 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 171 (accept_3_5 20 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 171 (accept_3_5 17 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 171 (accept_3_5 14 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 171 (Polychromatic418967fa.accept_27_13_7_9_1_9612 13 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 171
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 171 (accept_3_5 11 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 171 (accept_3_5 8 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 61 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 171 (accept_3_5 5 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 61 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 171 (accept_3_5 2 61 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 171 (allA_succ_of_accept 59 60 171 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 60 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 171
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 58 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 171 3 19 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 171 3 18 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 171
  (Polychromatic418967fa.accept_21_11_18_3_1_4862 53 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 171 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 171 3 17 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 171
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 171 3 16 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 171 (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 171 3 15 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 171
  (Polychromatic418967fa.accept_17_10_9_1_1_7062 44 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 171 3 14 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 171
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 171 3 13 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 171 (Polychromatic418967fa.accept_18_2_6_9_1_1032 38 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 171 (Polychromatic418967fa.accept_17_3_9_1_1_1344 37 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 171 3 12 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 171
  (Polychromatic418967fa.accept_14_7_4_3_1_488 35 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 171 3 11 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  32 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 171 3 10 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 171 (Polychromatic418967fa.accept_26_2_8_15_1_9611 28 60
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 171 3 9 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 171
  (Polychromatic418967fa.accept_16_10_12_11_1_346 26 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 171 (Polychromatic418967fa.accept_17_8_9_1_1_3340 25 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 171 3 8 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 171 3 7 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 171 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 171 3 6 20 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 171
  (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 171 (Polychromatic418967fa.accept_21_16_18_3_1_8050 16 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 171 3 5 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 171 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 171 3 4 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 171 (Polychromatic418967fa.accept_21_11_18_3_1_4862 11 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 60
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 171 3 3 20 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 171 3 2 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 171 (Polychromatic418967fa.accept_21_5_18_3_1_4908 5 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 171
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 60 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 171 3 1 20 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 171 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 60 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 171 (allA_succ_of_accept 58 59 171
  (accept_3_4 58 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 171 (accept_3_4 55 59 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 171 (Polychromatic418967fa.accept_15_9_14_6_1_3004 54 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 171
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 53 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 171 (accept_3_4 52 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 171 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 171 (accept_3_4 49 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 171
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 171 (accept_3_4 46 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 171 (accept_3_4 43 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 171
  (Polychromatic418967fa.accept_17_7_8_1_1_1373 41 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 171 (accept_3_4 40 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 171 (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 171 (accept_3_4 37 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 171 (Polychromatic418967fa.accept_21_15_17_3_1_3373 36 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 171 (accept_3_4 34 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 171 (accept_3_4 31 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 171 (Polychromatic418967fa.accept_18_12_5_9_1_6896 30 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 171
  (Polychromatic418967fa.accept_21_8_17_3_1_8031 29 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 171 (accept_3_4 28 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 171 (Polychromatic418967fa.accept_23_4_13_10_1_9610 27 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 171 (accept_3_4 25 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 171
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 171 (accept_3_4 22 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 171 (accept_3_4 19 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 171
  (Polychromatic418967fa.accept_24_17_11_3_1_9609 17 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 171 (accept_3_4 16 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 171 (accept_3_4 13 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 171
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 171 (accept_3_4 10 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 171 (accept_3_4 7 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 171 (Polychromatic418967fa.accept_22_6_15_17_1_4635 6 59 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 171 (accept_3_4 4 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  171 (Polychromatic418967fa.accept_23_3_13_10_1_9608 3 59 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 171 (accept_3_4 1 59 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 171
  (allA_succ_of_accept 57 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 171 (accept_3_5 56 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 54
  58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 171 (accept_3_5 53 58
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 171 (accept_3_5 50 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48
  58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 171 (accept_3_5 47 58
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 171
  (Polychromatic418967fa.accept_27_19_4_9_1_9607 46 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 171 (accept_3_5 44 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 171 (Polychromatic418967fa.accept_11_9_3_6_1_797
  42 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 171 (accept_3_5 41
  58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 171 (accept_3_5 38 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 171 (accept_3_5 35 58
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 171 (accept_3_5 32 58 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  30 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 171 (accept_3_5 29
  58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 171
  (Polychromatic418967fa.accept_16_12_10_11_1_2667 28 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 171 (accept_3_5 26 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 171
  (Polychromatic418967fa.accept_27_24_4_9_1_9606 24 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 171 (accept_3_5 23 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 171 (accept_3_5 20 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 171 (accept_3_5 17 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 171 (Polychromatic418967fa.accept_20_16_18_11_1_9605 16 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 171 (accept_3_5 14 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 171 (accept_3_5 11 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 171 (accept_3_5 8 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 171 (accept_3_5 5 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 58 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 171 (accept_3_5 2 58 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 171 (allA_succ_of_accept 56 57 171
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 171 3 18 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 171 3 17 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 171 3 16 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 171 3 15 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 171 3 14 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 171 3 13 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 57 171 19 2 3 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 171 3 12 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 171 3 11 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 171 3 10 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 171
  (Polychromatic418967fa.accept_20_8_17_11_1_9604 28 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 171 3 9 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 171 3 8 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 171 3 7 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 171 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 57 171 19 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 57 171 3 6 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 171 3 5 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 171 3 4 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 171 3 3 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 171
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 171 3 2 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 171 3 1 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 171 (allA_succ_of_accept 55 56 171
  (accept_3_4 55 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 171
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 171 (accept_3_4 52 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  50 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 171 (accept_3_4 49
  56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 171
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 48 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 171 (accept_3_4 46 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 171 (Polychromatic418967fa.accept_13_5_4_2_1_846
  44 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 171 (accept_3_4 43
  56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 56 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 171 (accept_3_4 40 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 56 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 171 (Polychromatic418967fa.accept_11_5_1_6_1_774
  38 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 171 (accept_3_4 37
  56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 171
  (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 171 (accept_3_4 34 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 56 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 56 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 171 (accept_3_4 31 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 171 (accept_3_4 28 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 56 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 171
  (Polychromatic418967fa.accept_20_6_16_11_1_2379 26 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 171 (accept_3_4 25 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 171 (accept_3_4 22 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 171 (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 56 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 171
  (Polychromatic418967fa.accept_15_5_11_6_1_692 20 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 171 (accept_3_4 19 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 171 (accept_3_4 16 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 56 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 171
  (Polychromatic418967fa.accept_22_14_12_17_1_9603 14 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 56 171 (accept_3_4 13 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 171 (accept_3_4 10 56 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 9
  56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 171
  (Polychromatic418967fa.accept_21_8_14_3_1_9602 8 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 171 (accept_3_4 7 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 171 (accept_3_4 4 56 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 56 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 171 (accept_3_4 1 56 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 171 (allA_succ_of_accept 54 55 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 171 (accept_3_5 53 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 171 (accept_3_5 50 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 171 (accept_3_5 47 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 171 (accept_3_5 44 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 171 (Polychromatic418967fa.accept_23_20_9_10_1_9601 43 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 171 (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 171 (accept_3_5 41 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 171 (accept_3_5 38 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 171 (accept_3_5 35 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 171 (accept_3_5 32 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 171 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 171 (accept_3_5 29 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 171
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 171 (accept_3_5 26 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 171 (accept_3_5 23 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 171 (accept_3_5 20 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 171 (accept_3_5 17 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 171
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 171 (accept_3_5 14 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 171 (Polychromatic418967fa.accept_20_13_15_11_1_6610 13 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 171 (accept_3_5 11 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 171 (accept_3_5 8 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  171 (Polychromatic418967fa.accept_22_7_11_17_1_9600 7 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 171 (accept_3_5 5 55 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 171
  (Polychromatic418967fa.accept_15_3_10_6_1_632 3 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 171 (accept_3_5 2 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 55 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 55 171))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 171
  (allA_succ_of_accept 53 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 171 3 17 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 171 3 16 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  47 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 54 171 9 5 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 54 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 171 3 14 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 171 3 13 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 171 (Polychromatic418967fa.accept_11_5_10_6_1_793
  38 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 171 9 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 171 3 11 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 171 3 10 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 54 171 9 3 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 54 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 171 3 8 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 171 3 7 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 171
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 171 9 2 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 171 3 5 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 171 3 4 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 54 171 9 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 54 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 171 3 2 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 171 3 1 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 171)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 171 (allA_succ_of_accept 52 53
  171 (accept_3_4 52 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 171
  (Polychromatic418967fa.accept_13_12_1_2_1_845 51 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 171 (accept_3_4 49 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 171 (Polychromatic418967fa.accept_11_3_9_6_1_105
  47 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 171 (accept_3_4 46
  53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 171
  (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 171 (accept_3_4 43 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 171 (accept_3_4 40 53
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 171
  (Polychromatic418967fa.accept_16_7_5_11_1_4777 39 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 171 (accept_3_4 37 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 171 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  35 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 171 (accept_3_4 34
  53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 171
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 171 (accept_3_4 31 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 171 (accept_3_4 28 53
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 171 (accept_3_4 25 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 171 (Polychromatic418967fa.accept_16_8_5_11_1_4776 24 53 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 171
  (Polychromatic418967fa.accept_16_7_5_11_1_4777 23 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 171 (accept_3_4 22 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 171 (accept_3_4 19 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 171 (accept_3_4 16 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 171 (accept_3_4 13 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 53 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 171
  (Polychromatic418967fa.accept_22_11_9_17_1_9599 11 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 171 (accept_3_4 10 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 171 (accept_3_4 7 53 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 171
  (Polychromatic418967fa.accept_23_5_7_10_1_9598 5 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 171 (accept_3_4 4 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 53 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 171 (accept_3_4 1 53 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 171))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 171
  (allA_succ_of_accept 51 52 171 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 171 (accept_3_5 50 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 171 (Polychromatic418967fa.accept_14_6_10_3_1_1038
  48 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 171 (accept_3_5 47
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 171 (Polychromatic418967fa.accept_27_18_25_9_1_9597 45 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 171 (accept_3_5 44 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 171 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 171 (accept_3_5 41
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 171
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 40 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 171 (accept_3_5 38 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 171 (Polychromatic418967fa.accept_10_6_2_1_1_494
  36 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 171 (accept_3_5 35
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 171 (accept_3_5 32 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 171 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 171 (accept_3_5 29
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 171
  (Polychromatic418967fa.accept_15_13_7_6_1_682 28 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 171 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 171 (accept_3_5 26 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 171 (Polychromatic418967fa.accept_16_8_4_11_1_2687
  24 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 171 (accept_3_5 23
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 171
  (Polychromatic418967fa.accept_16_6_4_11_1_1719 22 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 171 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 171 (accept_3_5 20 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 171 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 171 (accept_3_5 17
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 52 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 171 (accept_3_5 14 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 171 (Polychromatic418967fa.accept_15_12_7_6_1_4013
  12 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 171 (accept_3_5 11
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 171
  (Polychromatic418967fa.accept_27_10_25_9_1_9596 10 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 52 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 171 (accept_3_5 8 52 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 52 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 171 (accept_3_5 5 52 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 171 (Polychromatic418967fa.accept_23_4_6_10_1_7908
  4 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 171
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 171 (accept_3_5 2 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 171)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 171 (allA_succ_of_accept 50 51 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 171 3 16 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 171
  (Polychromatic418967fa.accept_16_14_3_11_1_5969 46 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 171 3 15 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 171 (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 171 3 14 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 171 3 13 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 171 (Polychromatic418967fa.accept_16_6_3_11_1_3751
  38 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 171
  (Polychromatic418967fa.accept_21_16_9_3_1_6436 37 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 171 3 12 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 171 (Polychromatic418967fa.accept_18_17_15_9_1_5542 35 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 171 3 11 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 171
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 171 (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 171 3 10 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 171
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 171 3 9 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 171 (Polychromatic418967fa.accept_27_25_24_9_1_9595 25 51
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 171 3 8 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 171
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 171 3 7 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 171 3 6 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 171 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 171 3 5 17 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 171
  (Polychromatic418967fa.accept_13_1_12_2_1_384 14 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 171 3 4 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 171 (Polychromatic418967fa.accept_18_11_15_9_1_360 11 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 171
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 171 3 3 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 171 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 171 3 2 17 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 171 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 51 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 171 3 1 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 171 (Polychromatic418967fa.accept_21_2_9_3_1_4841 2 51 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 171))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 171 (allA_succ_of_accept 49 50 171
  (accept_3_4 49 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 171
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 171 (accept_3_4 46 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 171 (accept_3_4 43 50
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 171
  (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 171 (accept_3_4 40 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 171 (Polychromatic418967fa.accept_16_6_2_11_1_7132
  38 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 171 (accept_3_4 37
  50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 171
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 171 (accept_3_4 34 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 171 (accept_3_4 31 50
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 171 (accept_3_4 28 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 50 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 171 (accept_3_4 25 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 171 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 171 (accept_3_4 22 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 171
  (Polychromatic418967fa.accept_27_20_23_9_1_9594 20 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 171 (accept_3_4 19 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 171 (accept_3_4 16 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 171 (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 50 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 171
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 171 (accept_3_4 13 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 171 (accept_3_4 10 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 171
  (Polychromatic418967fa.accept_22_8_6_17_1_9593 8 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 171 (accept_3_4 7 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 171 (accept_3_4 4 50 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 50 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  50 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 171 (accept_3_4 1 50 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 171)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 171 (allA_succ_of_accept 48 49 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 171 (accept_3_5 47 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 171 (accept_3_5 44 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 171 (accept_3_5 41 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 171
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 171 (accept_3_5 38 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 171 (Polychromatic418967fa.accept_21_15_7_3_1_4886 36 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 171 (accept_3_5 35 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 171 (accept_3_5 32 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 171 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 171 (accept_3_5 29 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 171
  (Polychromatic418967fa.accept_21_6_7_3_1_8073 27 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 171 (accept_3_5 26 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 171 (accept_3_5 23 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 171 (accept_3_5 20 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 171 (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 171 (accept_3_5 17 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 171 (accept_3_5 14 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 171 (accept_3_5 11 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 171 (accept_3_5 8 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  171 (Polychromatic418967fa.accept_23_7_3_10_1_2935 7 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 171 (accept_3_5 5 49 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 171
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 171 (accept_3_5 2 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  171 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 49 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 171))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 171 (allA_succ_of_accept 47 48 171
  (Polychromatic418967fa.accept_17_13_14_1_1_2258 47 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 171 3 15 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 171
  (Polychromatic418967fa.accept_10_3_8_1_1_182 43 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 171 3 14 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 171 3 13 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 171
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 171 3 12 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  35 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 171
  (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 171 3 11 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 171 3 10 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 171
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 171 (Polychromatic418967fa.accept_18_10_12_9_1_2012 28 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 171 3 9 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 171 3 8 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 171 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 48
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 171 3 7 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 171
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 171 3 6 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 171 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 48
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 171 3 5 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 171 3 4 16 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 171 3 3 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 171 (Polychromatic418967fa.accept_21_8_6_3_1_4881 8 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 171
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 171 3 2 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 171 3 1 16 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 48 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 171)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 171
  (allA_succ_of_accept 46 47 171 (accept_3_4 46 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 171 (accept_3_4 43 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 171 (accept_3_4 40 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 171 (Polychromatic418967fa.accept_16_7_15_11_1_951 39 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 171 (accept_3_4 37 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 171
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 35 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 171 (accept_3_4 34 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 171 (accept_3_4 31 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 171 (accept_3_4 28 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 171 (accept_3_4 25 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 171 (accept_3_4 22 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 171 (accept_3_4 19 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 171 (Polychromatic418967fa.accept_20_18_7_11_1_3692 18 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 171
  (Polychromatic418967fa.accept_16_1_15_11_1_356 17 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 171 (accept_3_4 16 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 171 (accept_3_4 13 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 171
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 11 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 171 (accept_3_4 10 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 171 (accept_3_4 7 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 47 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 171
  (Polychromatic418967fa.accept_22_5_3_17_1_9592 5 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 171 (accept_3_4 4 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  171 (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 47 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 171 (accept_3_4 1 47 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 171))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 171
  (allA_succ_of_accept 45 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 171 (accept_3_5 44 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  42 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 171 (accept_3_5 41
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 171
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 171 (Polychromatic418967fa.accept_15_9_1_6_1_657 39 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 171 (accept_3_5 38 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 171 (accept_3_5 35 46
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 171 (accept_3_5 32 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 171 (accept_3_5 29
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 171
  (Polychromatic418967fa.accept_21_7_4_3_1_6424 28 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 171 (accept_3_5 26 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 171 (Polychromatic418967fa.accept_15_9_1_6_1_657
  24 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 171 (accept_3_5 23
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 171 (accept_3_5 20 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 171 (accept_3_5 17
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 171
  (Polychromatic418967fa.accept_17_16_12_1_1_5785 16 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 171 (accept_3_5 14 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  12 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 171 (accept_3_5 11
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 171
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 171 (accept_3_5 8 46 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 171 (accept_3_5 5 46 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 4
  46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 171
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 171 (accept_3_5 2 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 171)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 171 (allA_succ_of_accept 44 45 171
  (Polychromatic418967fa.accept_10_4_5_1_1_497 44 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 171 3 14 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 171 3 13 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 171 9 4 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 171 3 11 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 171 (Polychromatic418967fa.accept_23_9_22_10_1_9591
  32 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 171 3 10 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 171 (Polychromatic418967fa.accept_22_6_1_17_1_9590 28 45
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 171 9 3 5 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 171 3 8 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 171 3 7 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 171 (Polychromatic418967fa.accept_22_20_1_17_1_9589 20 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 171 9 2 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 171 3 5 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 171 3 4 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 171 9 1 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 171
  (Polychromatic418967fa.accept_13_8_6_2_1_865 8 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 171 3 2 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 171
  (Polychromatic418967fa.accept_10_4_5_1_1_497 4 45 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 171 3 1 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  171))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 171 (allA_succ_of_accept 43 44 171 (accept_3_4 43 44
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 171
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 171 (accept_3_4 40 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173
  38 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 171 (accept_3_4 37
  44 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 171 (accept_3_4 34 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 171 (Polychromatic418967fa.accept_24_8_20_3_1_7857
  32 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 171 (accept_3_4 31
  44 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 171
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 171 (accept_3_4 28 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 171 (accept_3_4 25 44
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 171
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 171 (accept_3_4 22 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 171 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 171 (accept_3_4 19 44
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 171
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 171 (accept_3_4 16 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 171
  (Polychromatic418967fa.accept_17_14_10_1_1_4523 14 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 171 (accept_3_4 13 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 171 (accept_3_4 10 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 44 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 171 (accept_3_4 7 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 171 (accept_3_4 4 44 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 44 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 171 (Polychromatic418967fa.accept_23_2_21_10_1_9588
  2 44 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 171 (accept_3_4 1 44
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 171)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 171 (allA_succ_of_accept 42 43 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 171 (accept_3_5 41 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 171 (accept_3_5 38 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 171 (Polychromatic418967fa.accept_21_15_1_3_1_9587 36 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 171 (accept_3_5 35 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 171 (accept_3_5 32 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 171 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 171 (accept_3_5 29 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 171 (accept_3_5 26 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 171 (accept_3_5 23 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 171 (accept_3_5 20 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 171 (accept_3_5 17 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 171
  (Polychromatic418967fa.accept_17_15_9_1_1_3363 15 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 171 (accept_3_5 14 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 171 (Polychromatic418967fa.accept_20_13_3_11_1_9586 13 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 171 (accept_3_5 11 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 171 (accept_3_5 8 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  171 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 171 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 171 (accept_3_5 5 43 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 171
  (Polychromatic418967fa.accept_17_3_9_1_1_1344 3 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 171 (accept_3_5 2 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  171 (Polychromatic418967fa.accept_22_1_21_17_1_9585 1 43 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 43 171))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 171 (allA_succ_of_accept 41 42
  171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 171 3 13 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 38
  42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 171 3 12 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 171 3 11 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 171 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 171 3 10 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 171 3 9 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 171 3 8 14 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 171
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 171 3 7 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 171
  (Polychromatic418967fa.accept_10_9_2_1_1_840 19 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 171 3 6 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 171 3 5 14 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 171 3 4 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 171 3 3 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 171 3 2 14 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 171 3 1 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 171)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 171 (allA_succ_of_accept 40 41 171
  (accept_3_4 40 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 171 (accept_3_4 37 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 171 (Polychromatic418967fa.accept_15_5_11_6_1_692
  35 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 171 (accept_3_4 34
  41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 171
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 171 (accept_3_4 31 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 171
  (Polychromatic418967fa.accept_22_7_19_17_1_9584 29 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 171 (accept_3_4 28 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 171 (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 171 (accept_3_4 25 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 171 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 41 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 171 (accept_3_4 22 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 171 (accept_3_4 19 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 171
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 171 (accept_3_4 16 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 171 (Polychromatic418967fa.accept_18_15_5_9_1_5529 15 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 171 (accept_3_4 13 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 171 (Polychromatic418967fa.accept_18_12_5_9_1_6896 12 41 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 171 (accept_3_4 10 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 171 (accept_3_4 7 41 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 171
  (Polychromatic418967fa.accept_15_5_11_6_1_692 5 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 171 (accept_3_4 4 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 41 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 171 (accept_3_4 1 41 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 171))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 171 (allA_succ_of_accept 39 40 171
  (Polychromatic418967fa.accept_17_5_6_1_1_5735 39 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 171 (accept_3_5 38 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 171 (accept_3_5 35 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 40 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 171
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 171 (accept_3_5 32 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 171 (accept_3_5 29 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 171 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 40 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 171
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 171 (accept_3_5 26 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 171 (Polychromatic418967fa.accept_25_24_15_21_1_9583 24 40 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 171 (accept_3_5 23 40 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 171
  (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 171 (accept_3_5 20 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 171 (accept_3_5 17 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 171 (accept_3_5 14 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 171 (accept_3_5 11 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 171 (Polychromatic418967fa.accept_22_10_18_17_1_1830 10 40 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 171 (accept_3_5 8 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 40 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 171 (accept_3_5 5 40 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 171 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 40 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 171 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3
  40 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 171 (accept_3_5 2 40 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  171)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 171 (allA_succ_of_accept 38 39 171
  (Polychromatic418967fa.accept_10_8_9_1_1_189 38 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 171 (Polychromatic418967fa.accept_16_5_7_11_1_2664 37 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 171 3 12 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 171 3 11 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 171 3 10 13 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 171 3 9 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 171 3 8 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 171 (Polychromatic418967fa.accept_17_6_5_1_1_5754 23 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 171 3 7 13 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 171 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 171 3 6 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 171 (Polychromatic418967fa.accept_21_17_18_3_1_4909 17 39
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 171
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 171 3 5 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 171 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 171 3 4 13 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 171
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 171 (Polychromatic418967fa.accept_20_10_19_11_1_2384 10 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 171 3 3 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 171
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 171 3 2 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 171 3 1 13 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 171
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 39 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 171))))))))))))))))))))))))))))))))))))))) (allB_succ 38 171
  (allA_succ_of_accept 37 38 171 (accept_3_4 37 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 171 (accept_3_4 34 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 171 (accept_3_4 31 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 171 (accept_3_4 28 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 38 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 171
  (Polychromatic418967fa.accept_25_1_13_21_1_9581 26 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 171 (accept_3_4 25 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 171 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 171 (accept_3_4 22 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 38 171 19 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 38 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 171 (accept_3_4 16 38 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 171
  (Polychromatic418967fa.accept_21_15_17_3_1_3373 15 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 38 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 38 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 171 (accept_3_4 13 38 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 38 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 171 (accept_3_4 10 38
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 171
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 8 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 171 (accept_3_4 7 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 171 (accept_3_4 4 38 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 38 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 171 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2
  38 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 171 (accept_3_4 1 38 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 171)))))))))))))))))))))))))))))))))))))) (allB_succ 37 171
  (allA_succ_of_accept 36 37 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 171 (accept_3_5 35 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 171 (accept_3_5 32 37
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 171
  (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 171 (accept_3_5 29 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 171 (accept_3_5 26 37
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 171
  (Polychromatic418967fa.accept_16_9_5_11_1_3776 25 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 171 (accept_3_5 23 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 171 (accept_3_5 20
  37 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 171 (accept_3_5 17 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 171 (accept_3_5 14 37
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 171 (accept_3_5 11 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 171 (accept_3_5 8 37 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 171 (Polychromatic418967fa.accept_16_7_5_11_1_4777
  7 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 171 (accept_3_5 5 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 171 (accept_3_5 2 37 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 171))))))))))))))))))))))))))))))))))))) (allB_succ 36 171
  (allA_succ_of_accept 35 36 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 36
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 171 3 11 12 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 171 3 10 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 171 (Polychromatic418967fa.accept_13_3_10_2_1_381
  29 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 171
  (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 171 9 3 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 171 3 8 12 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 171 3 7 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 171 9 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 171 3 5 12 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 171
  (Polychromatic418967fa.accept_21_14_15_3_1_9580 14 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 171 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 171 3 4 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 171
  (Polychromatic418967fa.accept_21_10_15_3_1_6431 10 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 171 9 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 171 3 2 12 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 171 3 1 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 171
  (Polychromatic418967fa.accept_20_1_16_11_1_9579 1 36 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 171)))))))))))))))))))))))))))))))))))) (allB_succ 35 171 (allA_succ_of_accept 34 35 171 (accept_3_4 34
  35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 171
  (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 171 (accept_3_4 31 35 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 171 (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 35 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 171 (accept_3_4 28 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 171 (accept_3_4 25 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 171
  (Polychromatic418967fa.accept_16_7_3_11_1_3682 23 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 171 (accept_3_4 22 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 171 (accept_3_4 19 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 35 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 171
  (Polychromatic418967fa.accept_21_17_14_3_1_6411 17 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 171 (accept_3_4 16 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 171 (accept_3_4 13 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 35 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 171
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 171 (accept_3_4 10 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 171 (accept_3_4 7 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 35 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 171
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 171 (accept_3_4 4 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 35 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 171 (accept_3_4 1 35 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 171))))))))))))))))))))))))))))))))))) (allB_succ 34 171 (allA_succ_of_accept 33 34
  171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 171 (accept_3_5 32 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 171 (accept_3_5 29 34 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 171
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 171 (accept_3_5 26 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 171 (accept_3_5 23 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 171 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 34
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 171 (accept_3_5 20 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 171 (accept_3_5 17 34 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 171
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 171 (accept_3_5 14 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 171 (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 171 (accept_3_5 11 34 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 171 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 34
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 171 (accept_3_5 8 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 171 (accept_3_5 5 34 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 171 (Polychromatic418967fa.accept_20_3_14_11_1_6566
  3 34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 171 (accept_3_5 2 34
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  34 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 171))))))))))))))))))))))))))))))))))
  (allB_succ 33 171 (allA_succ_of_accept 32 33 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 33 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 171 3 10 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 171 3 9 11 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 171 3 8 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 171 3 7 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 171 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 171 3 6 11 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 171 3 5 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 171 3 4 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 171 3 3 11 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 171 3 2 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 171
  (Polychromatic418967fa.accept_18_4_15_9_1_6882 4 33 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 171 3 1 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 171)))))))))))))))))))))))))))))))))
  (allB_succ 32 171 (allA_succ_of_accept 31 32 171 (accept_3_4 31 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 32 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 171 (accept_3_4 28 32 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 171 (accept_3_4 25 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 171 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 171 (accept_3_4 22 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 32 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 171 (accept_3_4 19 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 171 (accept_3_4 16 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 171
  (Polychromatic418967fa.accept_13_1_6_2_1_377 14 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 171 (accept_3_4 13 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 171 (accept_3_4 10 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 32 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 171 (accept_3_4 7 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 171 (accept_3_4 4 32 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 32 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 171 (Polychromatic418967fa.accept_24_2_8_3_1_7844 2
  32 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 171 (accept_3_4 1 32 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 171)))))))))))))))))))))))))))))))) (allB_succ 31 171
  (allA_succ_of_accept 30 31 171 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 31 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 171 (accept_3_5 29 31 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 171
  (Polychromatic418967fa.accept_17_10_14_1_1_5823 27 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 171 (accept_3_5 26 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 171 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 171 (accept_3_5 23 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 171 (accept_3_5 20 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 171 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 171 (accept_3_5 17 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 171
  (Polychromatic418967fa.accept_21_15_10_3_1_9578 15 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 171 (accept_3_5 14 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 171 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 171 (accept_3_5 11 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 171 (accept_3_5 8 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  171 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 171 (Polychromatic418967fa.accept_18_6_13_9_1_4218 6 31 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 171 (accept_3_5 5 31 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3
  31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 171 (accept_3_5 2 31 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 171 (Polychromatic418967fa.accept_16_1_15_11_1_356
  1 31 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 171)))))))))))))))))))))))))))))))
  (allB_succ 30 171 (allA_succ_of_accept 29 30 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 30 171 3 9 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 30 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 171 3 8 10 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 171
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 23 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 171 3 7 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 30 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 171 3 6 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 171 3 5 10 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 171
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 171 3 4 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 30 171 3 3 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 30 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 171 (Polychromatic418967fa.accept_20_7_10_11_1_9577 7 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 171 3 2 10 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 171 3 1 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 171)))))))))))))))))))))))))))))) (allB_succ 29 171 (allA_succ_of_accept 28 29 171 (accept_3_4 28 29 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  27 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 171 (accept_3_4 25 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 171 (accept_3_4 22 29 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 171 (accept_3_4 19 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 171 (Polychromatic418967fa.accept_21_17_8_3_1_9576 17 29 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 171 (accept_3_4 16 29 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 171 (accept_3_4 13 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 171 (accept_3_4 10 29 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 171 (accept_3_4 7 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 171 (accept_3_4 4 29 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 171 (Polychromatic418967fa.accept_27_3_2_9_1_9575 3 29 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 171 (accept_3_4 1 29 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 171))))))))))))))))))))))))))))) (allB_succ 28 171
  (allA_succ_of_accept 27 28 171 (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 28 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 171 (accept_3_5 26 28 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 171
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 24 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 171 (accept_3_5 23 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 28 171 (Polychromatic418967fa.accept_20_1_8_11_1_8097 21 28 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 171 (accept_3_5 20 28 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 171 (accept_3_5 17 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 171 (Polychromatic418967fa.accept_21_16_7_3_1_8093 16 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 171 (accept_3_5 14 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 171
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 171 (accept_3_5 11 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 171 (Polychromatic418967fa.accept_16_10_12_11_1_346 10 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 171 (accept_3_5 8 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 171 (accept_3_5 5 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  171 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 28 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 28 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 171 (accept_3_5 2 28 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 171)))))))))))))))))))))))))))) (allB_succ 27 171
  (allA_succ_of_accept 26 27 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 171 3 8 9 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 171 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 171 3 7 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 171 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 171
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 171 9 2 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 171 3 5 9 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 171
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 171 (Polychromatic418967fa.accept_21_13_6_3_1_3381 13 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 171 3 4 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 171 9 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 171 (Polychromatic418967fa.accept_21_8_6_3_1_4881 8 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 171 3 2 9 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 171
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 171 3 1 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 27 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 171))))))))))))))))))))))))))) (allB_succ 26 171 (allA_succ_of_accept 25 26 171 (accept_3_4 25 26 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  24 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 171 (accept_3_4 22 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 171 (Polychromatic418967fa.accept_15_5_11_6_1_692 20 26 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 171 (accept_3_4 19 26 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 171 (accept_3_4 16 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 171 (Polychromatic418967fa.accept_20_14_6_11_1_6600 14 26 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 171 (accept_3_4 13 26 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 171 (accept_3_4 10 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 171 (accept_3_4 7 26 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 26 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 171 (accept_3_4 4 26 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083
  3 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 171 (accept_3_4 1 26 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  171)))))))))))))))))))))))))) (allB_succ 25 171 (allA_succ_of_accept 24 25 171
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 171 (accept_3_5 23 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 171 (accept_3_5 20 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 25 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 171 (accept_3_5 17 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 171 (accept_3_5 14 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 171
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 171 (accept_3_5 11 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 171 (accept_3_5 8 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 171 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 25 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 171 (accept_3_5 5 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 25 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 171 (accept_3_5 2 25 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 171))))))))))))))))))))))))) (allB_succ 24 171
  (allA_succ_of_accept 23 24 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 171 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 24
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 171 3 7 8 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 24 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 171 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 171 3 6 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 171
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 24 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 171 3 5 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 171 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 171 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 24
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 171 3 4 8 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 171
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 24 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 171 3 3 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 171 (Polychromatic418967fa.accept_17_8_7_1_1_4521 8 24 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 171
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 171 3 2 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 24 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 171 3 1 8 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 171
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 24 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 171 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 24 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 171)))))))))))))))))))))))) (allB_succ 23 171 (allA_succ_of_accept 22 23
  171 (accept_3_4 22 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 171
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 171 (accept_3_4 19 23 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 171 (Polychromatic418967fa.accept_15_2_8_6_1_1340
  17 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 171 (accept_3_4 16
  23 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 171 (accept_3_4 13 23 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 171
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 171 (accept_3_4 10 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 171 (accept_3_4 7 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 171 (accept_3_4 4 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  171 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 23 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 171 (accept_3_4 1 23 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 171))))))))))))))))))))))) (allB_succ 22 171 (allA_succ_of_accept 21 22 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 171 (accept_3_5 20 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 171 (accept_3_5 17 22 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 171
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 171 (accept_3_5 14 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 171 (accept_3_5 11 22 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 171 (Polychromatic418967fa.accept_21_10_1_3_1_8092 10 22 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 171 (accept_3_5 8 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 22 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 171 (accept_3_5 5 22 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3
  22 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 171 (accept_3_5 2 22 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 171)))))))))))))))))))))) (allB_succ 21
  171 (allA_succ_of_accept 20 21 171 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 21 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 171 (Polychromatic418967fa.accept_12_7_9_3_1_767
  19 21 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 171 3 6 7 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 21 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 171 3 5 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 171 3 4 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 171 3 3 7 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 171
  (Polychromatic418967fa.accept_16_8_5_11_1_4776 8 21 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 171 3 2 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 21 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 171
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 4 21 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 171 3 1 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 171))))))))))))))))))))) (allB_succ 20 171
  (allA_succ_of_accept 19 20 171 (accept_3_4 19 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 171 (accept_3_4 16 20 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 20 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 171 (accept_3_4 13 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 171 (accept_3_4 10 20 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 171
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 171 (accept_3_4 7 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 171 (accept_3_4 4 20 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 20 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  20 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 171 (accept_3_4 1 20 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 171)))))))))))))))))))) (allB_succ 19 171 (allA_succ_of_accept
  18 19 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 171 (accept_3_5 17 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 171 (accept_3_5 14 19 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  13 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 171
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 171 (accept_3_5 11 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 171 (accept_3_5 8 19 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 171 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 19 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 171
  (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 171 (accept_3_5 5 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 19 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 171 (accept_3_5 2 19 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 171))))))))))))))))))) (allB_succ 18 171 (allA_succ_of_accept 17
  18 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 171 3 5 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 171 3 4 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 18 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 171 9 1 2 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 171 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 18 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 171 3 2 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 171 3 1 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 171)))))))))))))))))) (allB_succ 17 171
  (allA_succ_of_accept 16 17 171 (accept_3_4 16 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 171 (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 171 (accept_3_4 13 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 171 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 17 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 171
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 171 (accept_3_4 10 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 171 (accept_3_4 7 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 171
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 171 (accept_3_4 4 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  171 (Polychromatic418967fa.accept_23_3_17_10_1_9574 3 17 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 171 (accept_3_4 1 17 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 171))))))))))))))))) (allB_succ 16 171 (allA_succ_of_accept 15 16 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 171 (accept_3_5 14 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 171 (accept_3_5 11 16 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 16 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 171
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 171 (accept_3_5 8 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 171 (accept_3_5 5 16 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 171 (Polychromatic418967fa.accept_23_4_16_10_1_9573 4 16 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 3
  16 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 171 (accept_3_5 2 16 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 171)))))))))))))))) (allB_succ 15 171
  (allA_succ_of_accept 14 15 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 15 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 15 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 171 3 4 5 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 171 (Polychromatic418967fa.accept_16_10_15_11_1_3785 10 15 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 171 3 3 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 171 (Polychromatic418967fa.accept_21_8_15_3_1_279 8 15 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 171
  (Polychromatic418967fa.accept_16_7_15_11_1_951 7 15 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 171 3 2 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 171 3 1 5 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 1 15 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 171))))))))))))))) (allB_succ 14 171 (allA_succ_of_accept 13 14 171
  (accept_3_4 13 14 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 171
  (Polychromatic418967fa.accept_13_12_1_2_1_845 12 14 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 171 (accept_3_4 10 14 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8
  14 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 171 (accept_3_4 7 14 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  14 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 171 (accept_3_4 4 14 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  171 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 14 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 14 171 (Polychromatic418967fa.accept_21_2_14_3_1_4933 2 14 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 171 (accept_3_4 1 14 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 14 171)))))))))))))) (allB_succ 13 171 (allA_succ_of_accept 12 13 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 171 (accept_3_5 11 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 171 (accept_3_5 8 13 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 13 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 171 (accept_3_5 5 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 171 (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 13 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 171 (accept_3_5 2 13 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 171 (Polychromatic418967fa.accept_23_1_13_10_1_9572 1 13 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 171))))))))))))) (allB_succ 12 171 (allA_succ_of_accept 11 12
  171 (Polychromatic418967fa.accept_18_11_12_9_1_992 11 12 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 12 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 12 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 171 3 3 4 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 171 3 2 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 12 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 171
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 12 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 171 3 1 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 171)))))))))))) (allB_succ 11 171
  (allA_succ_of_accept 10 11 171 (accept_3_4 10 11 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 171 (accept_3_4 7 11 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 171
  (Polychromatic418967fa.accept_15_5_11_6_1_692 5 11 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 171 (accept_3_4 4 11 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 11 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 11 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 171 (accept_3_4 1 11 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 11 171))))))))))) (allB_succ 10 171 (allA_succ_of_accept 9 10 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 171 (accept_3_5 8 10 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 10 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 171 (accept_3_5 5 10 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 171 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 10 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 3
  10 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 171 (accept_3_5 2 10 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 171)))))))))) (allB_succ 9 171
  (allA_succ_of_accept 8 9 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 171 3 2 3 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 171 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 9 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 171 3 1 3 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 171))))))))) (allB_succ 8 171 (allA_succ_of_accept 7 8 171 (accept_3_4 7 8 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 171 (accept_3_4 4 8 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 171
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 8 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 171 (accept_3_4 1 8 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 171)))))))) (allB_succ 7 171 (allA_succ_of_accept 6 7 171
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 7 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 171 (accept_3_5 5 7 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 171
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 171 (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 7 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 171 (accept_3_5 2 7 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 7 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 171))))))) (allB_succ 6 171 (allA_succ_of_accept 5 6 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 171 3 1 2 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 171)))))) (allB_succ 5 171 (allA_succ_of_accept 4 5 171 (accept_3_4 4 5 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 5 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 171 (accept_3_4 1 5 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 171))))) (allB_succ 4 171 (allA_succ_of_accept 3 4 171
  (Polychromatic418967fa.accept_26_3_4_15_1_9571 3 4 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 171 (accept_3_5 2 4 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 171
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 171)))) (allB_succ 3 171 (allA_succ_of_accept 2 3 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 3 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 171
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 3 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 171))) (allB_succ 2 171 (allA_succ_of_accept 1 2 171 (accept_3_4 1 2 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 171)) (allB_two
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


