-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch279_Segment002
-- name    : Polychromatic418967fa_Branch279_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:57:41.109492+00:00
-- url     : https://prove2.me/theorems/329137c4-29b1-4812-bbb3-a531b4e8db65
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch279_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_279_segment_002 : allB 180 279 :=
  allB_succ' 101 179 279 (Eq.refl Bool.true) (allA_succ_of_accept 100 179 279 (accept_3_4 100 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 179 279 (Polychromatic418967fa.accept_19_4_8_13_1_7802 99 179
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 179 279 (accept_3_4 97 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 179 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 95 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 179 279 (accept_3_4 94 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 179 279 (accept_3_4 91 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 179 279 (Polychromatic418967fa.accept_13_12_10_6_1_3212 90 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 179 279 (accept_3_4 88 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 179 279 (accept_3_4 85 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 179 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 179 279 (Polychromatic418967fa.accept_13_5_10_6_1_2361 83 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 179 279 (accept_3_4 82 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 179 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 179
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 179 279 (accept_3_4 79 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 179 279 (Polychromatic418967fa.accept_19_2_8_13_1_9146 78 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 179 279 (Polychromatic418967fa.accept_13_12_10_6_1_3212 77 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 179 279 (accept_3_4 76 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 179 279 (accept_3_4 73 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 179 279 (Polychromatic418967fa.accept_19_14_8_13_1_4834 71 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 279 (accept_3_4 70 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 179 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 179
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 179 279 (accept_3_4 67 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 179 279 (accept_3_4 64 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 179 279 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 179 279 (accept_3_4 61 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 279 (accept_3_4 58 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 279 (accept_3_4 55 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 279 (Polychromatic418967fa.accept_15_8_14_9_1_4216 53 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 279 (accept_3_4 52 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 279 (accept_3_4 49 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 279 (accept_3_4 46 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 279 (accept_3_4 43 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 279 (accept_3_4 40 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 279 (Polychromatic418967fa.accept_17_5_9_7_1_6185 39 179
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 279 (accept_3_4 37 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 279 (accept_3_4 34 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 279 (accept_3_4 31 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 279 (accept_3_4 28 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 27 179
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 279 (accept_3_4 25 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 279 (accept_3_4 22 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 279 (accept_3_4 19 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 279 (accept_3_4 16 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 279 (accept_3_4 13 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 279 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 279 (accept_3_4 10 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 179 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 279 (accept_3_4 7 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 279 (accept_3_4 4 179 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 179 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 279 (accept_3_4 1 179 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 178 279 (Eq.refl Bool.true) (allA_succ_of_accept 101 178 279 (accept_3_5 101 178 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 178 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 178 279
  (Polychromatic418967fa.accept_17_14_8_7_1_6183 99 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 178 279 (accept_3_5 98 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 178 279 (Polychromatic418967fa.accept_19_1_7_13_1_4813 96 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 178 279 (accept_3_5 95 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 94 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 178 279 (accept_3_5 92 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 178 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 178 279 (accept_3_5 89 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 178 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 178 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 178 279
  (Polychromatic418967fa.accept_10_7_8_9_1_785 87 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 178 279 (accept_3_5 86 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 178 279 (accept_3_5 83 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 178 279 (Polychromatic418967fa.accept_13_4_9_6_1_2376 82 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 178 279 (accept_3_5 80 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 178 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 178 279 (accept_3_5 77 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 178 279 (Polychromatic418967fa.accept_16_12_2_7_1_6853 76 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 178 279
  (Polychromatic418967fa.accept_11_9_2_4_1_707 75 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 178 279 (accept_3_5 74 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 178 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 178 279 (accept_3_5 71 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 178 279 (Polychromatic418967fa.accept_28_14_10_27_1_17141 70 178 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 178 279 (accept_3_5 68 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 178 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 178 279 (accept_3_5 65 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 178 279
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 63 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 178 279 (accept_3_5 62 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 178 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 178 279 (accept_3_5 59 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 178 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 178 279 (accept_3_5 56 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 178 279 (accept_3_5 53 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 178 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 178 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 178 279 (accept_3_5 50 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 178 279 (Polychromatic418967fa.accept_15_3_13_9_1_3196 48 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 178 279 (accept_3_5 47 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 178 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 178 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 178 279 (accept_3_5 44 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 178 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 178 279 (accept_3_5 41 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 178 279 (Polychromatic418967fa.accept_13_1_9_6_1_146 40 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 178 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 178 279 (accept_3_5 38 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 178 279 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 279 (accept_3_5 35 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 279 (accept_3_5 32 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 279 (accept_3_5 29 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 279
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 279 (accept_3_5 26 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 279 (accept_3_5 23 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 22 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 279 (accept_3_5 20 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 279 (accept_3_5 17 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 279
  (Polychromatic418967fa.accept_13_2_9_6_1_501 15 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 279 (accept_3_5 14 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 279 (Polychromatic418967fa.accept_16_12_2_7_1_6853 12 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 279 (accept_3_5 11 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 279 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 178
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 279 (accept_3_5 8 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 279 (accept_3_5 5 178 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 178 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 279
  (Polychromatic418967fa.accept_13_3_9_6_1_502 3 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 279 (accept_3_5 2 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 177 279 (Eq.refl Bool.true) (allA_succ_of_gcd 102 177 279 3 34 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 177 279 (Polychromatic418967fa.accept_7_3_2_6_1_56
  101 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 177 279
  (Polychromatic418967fa.accept_15_10_12_9_1_776 100 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 177 279 3 33 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 177 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 97 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 177 279 3 32 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 177 279 3 31 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 177 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 177 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 177 279 3 30 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 177 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 89
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 177 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 88 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 177 279 3 29 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 85
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 177 279 3 28 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 177 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 83 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 177 279 3 27 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 177 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 177 279 3 26 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 177 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 279
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 76 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 177 279 3 25 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 73
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 177 279 3 24 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 177 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 177 279 3 23 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 177 279 (Polychromatic418967fa.accept_10_8_7_9_1_425
  68 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 177 279 3 22 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 177 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 64
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 177 279 3 21 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 177 279 3 20 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 177 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 177 279 3 19 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 279 (Polychromatic418967fa.accept_16_8_1_7_1_2355 56 177 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 177 279 3 18 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 52
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 279 3 17 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 177 279 3 16 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 177 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 279 3 15 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 279 (Polychromatic418967fa.accept_15_14_12_9_1_3216 44 177 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 177 279 3 14 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 177 279 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 177 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 279
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 40 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 279 3 13 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 279 3 12 59 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 279 3 11 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 279 3 10 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 279 (Polychromatic418967fa.accept_10_8_7_9_1_425
  28 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 279 3 9 59 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 279 3 8 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 279 3 7 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 279 (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 279 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 177
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 279 3 6 59 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 279 (Polychromatic418967fa.accept_18_16_15_9_1_6852 16 177 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 279 3 5 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 279 3 4 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 279 3 3 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 177 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 279 3 2 59 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 279 3 1 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 177 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 176 279 (Eq.refl Bool.true) (allA_succ_of_accept 103 176 279 (accept_3_4 103 176 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 176 279 (accept_3_4 100 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 176 279 (Polychromatic418967fa.accept_17_14_6_7_1_4980 99 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 176 279 (Polychromatic418967fa.accept_17_13_6_7_1_4999 98 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 176 279 (accept_3_4 97 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 176 279 (accept_3_4 94 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 176 279 (Polychromatic418967fa.accept_13_1_7_6_1_142 92 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 176 279 (accept_3_4 91 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 176 279 (accept_3_4 88 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 176 279 (Polychromatic418967fa.accept_13_9_7_6_1_1673 87 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 86 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 176 279 (accept_3_4 85 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 176 279 (Polychromatic418967fa.accept_17_16_6_7_1_2715 84 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 176 279 (accept_3_4 82 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 176 279 (Polychromatic418967fa.accept_15_6_11_9_1_3215 81 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 176 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 80 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 176 279 (accept_3_4 79 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 176 279 (accept_3_4 76 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 176 279 (Polychromatic418967fa.accept_13_9_7_6_1_1673 74 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 176 279 (accept_3_4 73 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 176 279 (accept_3_4 70 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 176 279 (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 176 279 (accept_3_4 67 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 176 279 (accept_3_4 64 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 176 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 176 279 (Polychromatic418967fa.accept_15_2_11_9_1_263 62 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 176 279 (accept_3_4 61 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 176 279 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 176
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 176 279 (accept_3_4 58 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 176 279 (Polychromatic418967fa.accept_18_3_14_9_1_4264 57 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 176 279 (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 176 279 (accept_3_4 55 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 176 279 (accept_3_4 52 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 176 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 50 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 176 279 (accept_3_4 49 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 176 279 (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 176
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 176 279 (accept_3_4 46 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 176 279 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 176 279 (accept_3_4 43 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 176 279 (accept_3_4 40 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 176 279 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 176 279 (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 176 279 (accept_3_4 37 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 176 279 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 176
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 176 279 (accept_3_4 34 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 176 279 (Polychromatic418967fa.accept_15_2_11_9_1_263 32 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 176 279 (accept_3_4 31 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 176 279 (accept_3_4 28 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 176 279 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 176 279 (accept_3_4 25 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 176 279 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 176 279 (accept_3_4 22 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 176 279 (Polychromatic418967fa.accept_14_7_8_13_1_3161 21 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 176 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 279 (accept_3_4 19 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 279 (accept_3_4 16 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 279 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 279 (Polychromatic418967fa.accept_13_1_7_6_1_142 14 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 279 (accept_3_4 13 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 176 279 (accept_3_4 10 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 176 279 (Polychromatic418967fa.accept_19_8_5_13_1_7800 8 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 279 (accept_3_4 7 176 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 176 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 176 279 (accept_3_4 4 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  176 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 176 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 176 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 279 (accept_3_4 1 176 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 175 279 (Eq.refl Bool.true) (allA_succ_of_accept 104 175 279 (accept_3_5 104 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 175 279 (Polychromatic418967fa.accept_19_8_4_13_1_4912 103
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 175 279
  (Polychromatic418967fa.accept_15_12_10_9_1_798 102 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 175 279 (accept_3_5 101 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 175 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 99 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 175 279 (accept_3_5 98 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 175 279
  (Polychromatic418967fa.accept_17_12_5_7_1_6179 97 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 175 279 (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 175 279 (accept_3_5 95 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 175 279
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 175 279 (accept_3_5 92 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 175 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 91 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 175 279 (Polychromatic418967fa.accept_14_6_7_13_1_3158 90 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 175 279 (accept_3_5 89 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 175 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 175 279
  (Polychromatic418967fa.accept_15_12_10_9_1_798 87 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 175 279 (accept_3_5 86 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 175 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 85 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 175 279 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 175 279 (accept_3_5 83 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 175 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 175 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 81 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 175 279 (accept_3_5 80 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 175 279 (Polychromatic418967fa.accept_15_4_10_9_1_4298 79 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 175 279 (Polychromatic418967fa.accept_14_8_7_13_1_4113 78 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 175 279 (accept_3_5 77 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 175 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 175 279
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 75 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 175 279 (accept_3_5 74 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 175 279 (Polychromatic418967fa.accept_27_19_13_9_1_17140 73 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 279
  (Polychromatic418967fa.accept_15_12_10_9_1_798 72 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 175 279 (accept_3_5 71 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 175 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 279 (accept_3_5 68 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 67 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 175 279
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 175 279 (accept_3_5 65 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 175 279 (Polychromatic418967fa.accept_15_3_10_9_1_769 63 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 279 (accept_3_5 62 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 175 279
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 175 279 (accept_3_5 59 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 175 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 279 (accept_3_5 56 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 175 279 (Polychromatic418967fa.accept_19_17_4_13_1_4828 55 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 279
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 279 (accept_3_5 53 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 279 (accept_3_5 50 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 279
  (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 279 (accept_3_5 47 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 279 (accept_3_5 44 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 279
  (Polychromatic418967fa.accept_15_12_10_9_1_798 42 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 279 (accept_3_5 41 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 279 (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 279 (accept_3_5 38 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 279 (Polychromatic418967fa.accept_20_17_15_19_1_12975 37
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 279
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 279 (accept_3_5 35 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 279 (accept_3_5 32 175 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 279
  (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 175 279 (accept_3_5 29 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 279 (accept_3_5 26 175
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 279
  (Polychromatic418967fa.accept_19_6_4_13_1_2329 25 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 175 279 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 279 (accept_3_5 23 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 279 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 279 (accept_3_5 20
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 279
  (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 279 (Polychromatic418967fa.accept_15_3_10_9_1_769 18 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 279 (accept_3_5 17 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 279 (Polychromatic418967fa.accept_14_1_7_13_1_333
  15 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 279 (accept_3_5 14
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 279
  (Polychromatic418967fa.accept_21_13_7_6_1_3656 13 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 279 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 279 (accept_3_5 11 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 279 (accept_3_5 8
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 279
  (Polychromatic418967fa.accept_19_7_4_13_1_6319 7 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 175 279 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 279 (accept_3_5 5 175 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 175 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 279 (Polychromatic418967fa.accept_15_3_10_9_1_769
  3 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 279 (accept_3_5 2
  175 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 175 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 175
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 174 279 (Eq.refl Bool.true) (allA_succ_of_gcd 105 174 279 3 35 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 174 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 104 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 174 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 103 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 174 279 3 34 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 101
  174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 174 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 100 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 174 279 3 33 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 174 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 174 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 97 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 174 279 3 32 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 174 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 95 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 174 279 (Polychromatic418967fa.accept_12_10_6_3_1_786
  94 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 174 279 3 31 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 174 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 92 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 174 279 (Polychromatic418967fa.accept_14_7_6_13_1_4111 91 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 174 279 3 30 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 89
  174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 174 279
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 174 279 3 29 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 174 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 86 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 174 279 3 28 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 174 279
  (Polychromatic418967fa.accept_10_3_4_9_1_15 83 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 174 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 82 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 174 279 3 27 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 174 279 (Polychromatic418967fa.accept_12_8_6_3_1_366
  80 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 174 279
  (Polychromatic418967fa.accept_11_2_9_4_1_310 79 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 279 3 26 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 174 279 (Polychromatic418967fa.accept_12_4_6_3_1_332
  76 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 174 279 3 25 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 174 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 174 279 3 24 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 174 279 (Polychromatic418967fa.accept_17_3_4_7_1_1658
  71 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 174 279
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 174 279 3 23 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 174 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 174 279
  (Polychromatic418967fa.accept_19_10_3_13_1_6284 67 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 174 279 3 22 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 174 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 174 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 174 279 3 21 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 174 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 174 279 3 20 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 174 279
  (Polychromatic418967fa.accept_17_8_4_7_1_7442 59 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 174 279 3 19 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 174 279 (Polychromatic418967fa.accept_12_8_6_3_1_366
  56 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 279
  (Polychromatic418967fa.accept_10_5_4_9_1_420 55 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 279 3 18 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 279 (Polychromatic418967fa.accept_12_4_6_3_1_332
  52 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 174 279 3 17 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 174 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 174 279 3 16 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 174 279 (Polychromatic418967fa.accept_14_5_6_13_1_3145
  47 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 279
  (Polychromatic418967fa.accept_11_2_9_4_1_310 46 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 174 279 3 15 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 174 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 279 (Polychromatic418967fa.accept_10_3_4_9_1_15
  43 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 279 3 14 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 174 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 174 279 3 13 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 279 3 12 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 279 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 174 279 3 11 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 174 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 174 279 (Polychromatic418967fa.accept_16_15_14_7_1_10555 31 174 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 174 279 3 10 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 174 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 174 279 3 9 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 174 279 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 279 3 8 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 174
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 174 279 3 7 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 174 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 279 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 279 3 6 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 174 279 3 5 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 174 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 279 3 4 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 279
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 279 3 3 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 174 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 279
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 279 3 2 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 174 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 174 279 3 1 58 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 279
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 174 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 173 279 (Eq.refl Bool.true) (allA_succ_of_accept 106 173 279 (accept_3_4 106 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 105 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 173 279 (accept_3_4 103 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 173 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 101 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 173 279 (accept_3_4 100 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 173 279 (accept_3_4 97 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 173 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 96 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 173 279 (accept_3_4 94 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 173 279 (accept_3_4 91 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 173 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 89 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 173 279 (accept_3_4 88 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 173 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 87 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 279 (accept_3_4 85 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371 83 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 279 (accept_3_4 82 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 173 279 (accept_3_4 79 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 77 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 279 (accept_3_4 76 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 75 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 279 (accept_3_4 73 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 279 (accept_3_4 70 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 279 (accept_3_4 67 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 279 (Polychromatic418967fa.accept_19_8_2_13_1_2328 65 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 279 (accept_3_4 64 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 279 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 279 (accept_3_4 61 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 59 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 279 (accept_3_4 58 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 279 (accept_3_4 55 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 279 (accept_3_4 52 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 279 (accept_3_4 49 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 48 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 47 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 279 (accept_3_4 46 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 279 (accept_3_4 43 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 279 (accept_3_4 40 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 279 (accept_3_4 37 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 279 (accept_3_4 34 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 279 (accept_3_4 31 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 279 (accept_3_4 28 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 279 (Polychromatic418967fa.accept_17_10_3_7_1_1679 27 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 279 (accept_3_4 25 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 279 (accept_3_4 22 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 173
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 279 (accept_3_4 19 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 279 (accept_3_4 16 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 173 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 279 (accept_3_4 13 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 279 (accept_3_4 10 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 279 (accept_3_4 7 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 279 (accept_3_4 4 173 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 173 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 279 (accept_3_4 1 173 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 172 279 (Eq.refl Bool.true) (allA_succ_of_accept 107 172 279 (accept_3_5 107 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 172 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 106 172
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 172 279
  (Polychromatic418967fa.accept_13_1_3_6_1_158 105 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 172 279 (accept_3_5 104 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 172 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 102 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 172 279 (accept_3_5 101 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 172 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 172
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 172 279
  (Polychromatic418967fa.accept_8_3_4_7_1_475 99 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 172 279 (accept_3_5 98 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 172 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 172 279 (accept_3_5 95 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 172 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 172 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 172 279 (accept_3_5 92 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 172 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 172 279 (accept_3_5 89 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 172 279 (Polychromatic418967fa.accept_13_10_3_6_1_1003 88 172
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 172 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 172 279 (accept_3_5 86 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 172 279 (Polychromatic418967fa.accept_16_4_12_7_1_4475 84 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 172 279 (accept_3_5 83 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 172 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 172 279
  (Polychromatic418967fa.accept_10_1_2_9_1_152 81 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 172 279 (accept_3_5 80 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 172 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 172 279 (accept_3_5 77 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 172 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 76 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 172 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 172 279 (accept_3_5 74 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 172 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 172 279 (accept_3_5 71 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 172 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 172 279
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 172 279 (accept_3_5 68 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 172 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 172 279 (accept_3_5 65 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 172 279 (Polychromatic418967fa.accept_17_13_2_7_1_6122 64 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 172 279
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 172 279 (accept_3_5 62 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 172 279 (Polychromatic418967fa.accept_17_9_2_7_1_2689 60 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 172 279 (accept_3_5 59 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 172 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 279
  (Polychromatic418967fa.accept_10_7_2_9_1_775 57 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 172 279 (accept_3_5 56 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 172 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 279 (accept_3_5 53 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 172 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 172 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 172 279 (accept_3_5 50 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 172 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 279 (accept_3_5 47 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 172 279 (accept_3_5 44 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 172 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 279 (accept_3_5 41 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 279
  (Polychromatic418967fa.accept_21_18_4_6_1_6697 39 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 279 (accept_3_5 38 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 279 (accept_3_5 35 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 34 172
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 279 (accept_3_5 32 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 279 (accept_3_5 29 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 279 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 279
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 279 (accept_3_5 26 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 279 (accept_3_5 23 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 279
  (Polychromatic418967fa.accept_10_1_2_9_1_152 21 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 279 (accept_3_5 20 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 279 (accept_3_5 17 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 172 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 279
  (Polychromatic418967fa.accept_17_15_2_7_1_7389 15 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 279 (accept_3_5 14 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 279 (accept_3_5 11 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 279 (accept_3_5 8 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 279 (accept_3_5 5 172 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 279 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 172 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 279 (accept_3_5 2 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 171 279 (Eq.refl Bool.true) (allA_succ_of_gcd 108 171 279 9 12 19 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 171 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 107 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 171 279 (Polychromatic418967fa.accept_15_1_6_9_1_254 106 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 171 279 3 35 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 171 279
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 104 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 171 279 (Polychromatic418967fa.accept_13_12_2_6_1_2396 103 171 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 171 279 3 34 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 171 279
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 101 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 171 279 9 11 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 171 279 (Polychromatic418967fa.accept_10_8_1_9_1_413
  98 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 171 279
  (Polychromatic418967fa.accept_21_13_3_6_1_8232 97 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 171 279 3 32 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 95 171 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 279
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 94 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 171 279 3 31 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 171 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 92 171 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 279
  (Polychromatic418967fa.accept_15_1_6_9_1_254 91 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 171 279 9 10 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 171 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274 89 171 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 88 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 171 279 3 29 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 171 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 171 279 (Polychromatic418967fa.accept_10_5_1_9_1_791
  85 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 171 279 3 28 57 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 171 279
  (Polychromatic418967fa.accept_16_3_11_7_1_770 83 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 171 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 82 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 171 279 9 9 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 171 279
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 80 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 171 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 171 279 3 26 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 171 279
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 77 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 171 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 171 279 3 25 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 74
  171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 171 279
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 73 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 171 279 9 8 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 171 279 (Polychromatic418967fa.accept_15_11_6_9_1_3236 71 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 279 (Polychromatic418967fa.accept_20_10_11_19_1_10084 70
  171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 171 279 3 23 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 171 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 68 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 171 279 3 22 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 65
  171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 279
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 64 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 279 9 7 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 171 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 62 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 279 (Polychromatic418967fa.accept_13_9_2_6_1_514 61 171
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 279 3 20 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 279
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 279 3 19 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 279 (Polychromatic418967fa.accept_13_4_2_6_1_1043
  56 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 279 9 6 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 171 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 279 3 17 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 279
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 50 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 279 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 171 279 3 16 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 171 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385
  47 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 279 9 5 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 279 (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 171
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 279 3 14 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 279
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 41 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 279 (Polychromatic418967fa.accept_13_1_2_6_1_515 40 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 279 3 13 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 279 (Polychromatic418967fa.accept_10_8_1_9_1_413
  38 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 171 279 9 4 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 171 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385 34 171
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 279 3 11 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 279 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 279 3 10 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 171 279 9 3 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 279 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 171 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 279 3 8 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 279 3 7 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 20
  171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 279
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 171 279 9 2 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 279 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 279 3 5 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 279
  (Polychromatic418967fa.accept_13_1_2_6_1_515 14 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 279 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 279 3 4 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 279
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 279 9 1 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 279 (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 171 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 279 3 2 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 279 3 1 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 279
  (Polychromatic418967fa.accept_13_1_2_6_1_515 1 171 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 170 279 (Eq.refl Bool.true) (allA_succ_of_accept 109 170 279 (accept_3_4 109 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 170 279 (accept_3_4 106 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 170 279 (Polychromatic418967fa.accept_15_14_5_9_1_2284 104 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 170 279 (accept_3_4 103 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 170 279 (accept_3_4 100 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 170 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 98 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 170 279 (accept_3_4 97 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 170 279 (Polychromatic418967fa.accept_13_5_1_6_1_2367 96 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 170 279 (accept_3_4 94 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 170 279 (accept_3_4 91 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 170 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 170 279 (accept_3_4 88 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 170 279 (Polychromatic418967fa.accept_13_8_1_6_1_997 86 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 170 279 (accept_3_4 85 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 170 279 (Polychromatic418967fa.accept_19_8_18_13_1_11803 84
  170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 170 279 (accept_3_4 82 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 80 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 170 279 (accept_3_4 79 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 170 279 (accept_3_4 76 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 170 279 (Polychromatic418967fa.accept_18_3_8_9_1_1956 75 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 170 279 (accept_3_4 73 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 170 279 (Polychromatic418967fa.accept_13_7_1_6_1_3287 72 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 170 279 (accept_3_4 70 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 170 279 (Polychromatic418967fa.accept_13_3_1_6_1_509 68 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 170 279 (accept_3_4 67 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 170 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 170 279 (accept_3_4 64 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 170 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 63 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 170 279 (Polychromatic418967fa.accept_16_14_10_7_1_2363 62 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 170 279 (accept_3_4 61 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 170 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 170 279 (accept_3_4 58 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 170 279 (Polychromatic418967fa.accept_15_11_5_9_1_3205 56 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 170 279 (accept_3_4 55 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 170 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 170 279 (accept_3_4 52 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 170 279 (Polychromatic418967fa.accept_16_3_10_7_1_4518 51 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 170 279 (accept_3_4 49 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 170 279 (Polychromatic418967fa.accept_13_9_1_6_1_510 48 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 170 279 (accept_3_4 46 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 170 279 (Polychromatic418967fa.accept_13_5_1_6_1_2367 44 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 170 279 (accept_3_4 43 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 170 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 170 279 (accept_3_4 40 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 279 (accept_3_4 37 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 170 279 (accept_3_4 34 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 279 (accept_3_4 31 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 170 279 (accept_3_4 28 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 170 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 170 279 (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 279 (accept_3_4 25 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 170 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 170 279 (accept_3_4 22 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 170 279 (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 279 (accept_3_4 19 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 170 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 170 279 (accept_3_4 16 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 170 279 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 279 (accept_3_4 13 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 170
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 170 279 (accept_3_4 10 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  170 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 170 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 279 (accept_3_4 7 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 170 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 170 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 170 279 (accept_3_4 4 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  170 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 170 279 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 279 (accept_3_4 1 170 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 169 279 (Eq.refl Bool.true) (allA_succ_of_accept 110 169 279 (accept_3_5 110 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 169 279 (Polychromatic418967fa.accept_16_13_9_7_1_4532 109
  169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 169 279
  (Polychromatic418967fa.accept_17_6_16_7_1_12533 108 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 169 279 (accept_3_5 107 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 169 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 105 169
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 169 279 (accept_3_5 104 169
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 169 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 169 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 279 (accept_3_5 101 169 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 279
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 99 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 279 (accept_3_5 98 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 279 (Polychromatic418967fa.accept_23_5_8_3_1_17139 97 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 169 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 279 (accept_3_5 95 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 279 (accept_3_5 92 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 279 (Polychromatic418967fa.accept_14_7_1_13_1_357 91 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 279 (accept_3_5 89 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 279
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 87 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 169 279 (accept_3_5 86 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 169 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 85 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 169 279 (Polychromatic418967fa.accept_20_4_9_19_1_766 84 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 279 (accept_3_5 83 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 279
  (Polychromatic418967fa.accept_12_9_1_3_1_350 81 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 279 (accept_3_5 80 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 279 (accept_3_5 77 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 279 (accept_3_5 74 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 279 (Polychromatic418967fa.accept_15_13_4_9_1_2283 73 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 279 (accept_3_5 71 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 279
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 279 (accept_3_5 68 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 279 (Polychromatic418967fa.accept_16_3_9_7_1_6842 67 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 279 (accept_3_5 65 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 279
  (Polychromatic418967fa.accept_14_7_1_13_1_357 63 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 279 (accept_3_5 62 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 279 (Polychromatic418967fa.accept_18_6_7_9_1_4250 60 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 279 (accept_3_5 59 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 279
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 279 (accept_3_5 56 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 55 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 279 (accept_3_5 53 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 279 (accept_3_5 50 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 279 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 279 (Polychromatic418967fa.accept_20_8_9_19_1_8713 48 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 279 (accept_3_5 47 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 279
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 279 (accept_3_5 44 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 279 (Polychromatic418967fa.accept_15_13_4_9_1_2283 43 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 279 (accept_3_5 41 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 279
  (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 279 (accept_3_5 38 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 279 (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 279 (accept_3_5 35 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 279 (accept_3_5 32 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 279 (Polychromatic418967fa.accept_25_6_19_4_1_17138 31 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 279 (accept_3_5 29 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 279
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 279 (accept_3_5 26 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 279 (Polychromatic418967fa.accept_16_8_9_7_1_768 24 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 279 (accept_3_5 23 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 279
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 279 (accept_3_5 20 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 279 (accept_3_5 17 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 279
  (Polychromatic418967fa.accept_19_15_17_13_1_4901 15 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 169 279 (accept_3_5 14 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 169 279 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 169 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 279 (accept_3_5 11 169 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 279 (accept_3_5 8 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 279 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 279 (accept_3_5 5 169 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 279
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 3 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 279 (accept_3_5 2 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 279 (Polychromatic418967fa.accept_25_1_19_4_1_8396 1 169 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 168 279 (Eq.refl Bool.true) (allA_succ_of_gcd 111 168 279 3 37 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 168 279
  (Polychromatic418967fa.accept_15_5_3_9_1_283 110 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 168 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 109 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 168 279 3 36 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 168 279
  (Polychromatic418967fa.accept_10_7_8_9_1_785 107 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 168 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 106 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 168 279 3 35 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784
  104 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 168 279
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 103 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 168 279 3 34 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 168 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 101 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 168 279
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 100 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 168 279 3 33 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 168 279 (Polychromatic418967fa.accept_13_7_12_6_1_1039 98 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 168 279
  (Polychromatic418967fa.accept_10_7_8_9_1_785 97 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 168 279 3 32 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 168 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 95 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784
  94 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 168 279 3 31 56 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 168 279
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 92 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 168 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 91 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 168 279 3 30 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 168 279 (Polychromatic418967fa.accept_16_9_8_7_1_4529
  89 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 168 279
  (Polychromatic418967fa.accept_13_10_12_6_1_991 88 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 168 279 3 29 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 168 279 (Polychromatic418967fa.accept_18_14_6_9_1_1950 86 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 168 279
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 85 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 168 279 3 28 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 168 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 83 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 168 279
  (Polychromatic418967fa.accept_26_4_12_19_1_15418 82 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 168 279 3 27 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 168 279 (Polychromatic418967fa.accept_13_2_12_6_1_2394 80 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 168 279
  (Polychromatic418967fa.accept_16_15_8_7_1_3407 79 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 279 3 26 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 168 279
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 76 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 168 279 3 25 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 74 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 168 279 (Polychromatic418967fa.accept_11_7_3_4_1_729
  73 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 168 279 3 24 56 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 168 279
  (Polychromatic418967fa.accept_10_1_8_9_1_787 71 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 168 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 70 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 168 279 3 23 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 168 279 (Polychromatic418967fa.accept_15_8_3_9_1_4220
  68 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 168 279
  (Polychromatic418967fa.accept_10_7_8_9_1_785 67 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 279 3 22 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 279 (Polychromatic418967fa.accept_15_5_3_9_1_283 65 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784
  64 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 168 279 3 21 56 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 168 279
  (Polychromatic418967fa.accept_11_7_3_4_1_729 62 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 168 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 279 3 20 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 279 (Polychromatic418967fa.accept_13_7_12_6_1_1039
  59 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 279
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 58 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 168 279 3 19 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 168 279 (Polychromatic418967fa.accept_17_5_15_7_1_4992 56 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 168 279
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 55 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 279 3 18 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 279 (Polychromatic418967fa.accept_15_8_3_9_1_4220 53 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 279
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 168 279 3 17 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 168 279 (Polychromatic418967fa.accept_15_5_3_9_1_283 50 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 279
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 279 3 16 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 279
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 46 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 168 279 3 15 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 279
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 279 3 14 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 279 (Polychromatic418967fa.accept_11_7_3_4_1_729
  40 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 168 279 3 13 56 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 168 279
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 38 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 168 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 279 3 12 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 279 (Polychromatic418967fa.accept_15_5_3_9_1_283
  35 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 279
  (Polychromatic418967fa.accept_10_4_8_9_1_784 34 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 168 279 3 11 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 168 279 (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 168 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 279
  (Polychromatic418967fa.accept_10_1_8_9_1_787 31 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 279 3 10 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 168 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 279
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 168 279 3 9 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 168 279 (Polychromatic418967fa.accept_17_9_15_7_1_6212 26 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 279 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 168
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 279 3 8 56 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 279
  (Polychromatic418967fa.accept_13_10_12_6_1_991 23 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 279 (Polychromatic418967fa.accept_17_5_15_7_1_4992 22 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 279 3 7 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 279 (Polychromatic418967fa.accept_13_7_12_6_1_1039
  20 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 279
  (Polychromatic418967fa.accept_17_2_15_7_1_6213 19 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 279 3 6 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 279 (Polychromatic418967fa.accept_23_16_7_3_1_10710 16 168
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 279 3 5 56 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 168 279
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 279 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 279 3 4 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 279 (Polychromatic418967fa.accept_10_1_8_9_1_787
  11 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 279
  (Polychromatic418967fa.accept_13_10_12_6_1_991 10 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 168 279 3 3 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 168 279 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 168 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 279 3 2 56 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 279
  (Polychromatic418967fa.accept_13_5_12_6_1_508 5 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 168 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 279 3 1 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 279 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 168 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 279
  (Polychromatic418967fa.accept_10_1_8_9_1_787 1 168 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 167 279 (Eq.refl Bool.true) (allA_succ_of_accept 112 167 279 (accept_3_4 112 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 167 279 (Polychromatic418967fa.accept_19_16_15_13_1_1335 111
  167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 167 279 (accept_3_4 109 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 167 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 108 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 167 279 (Polychromatic418967fa.accept_21_2_20_6_1_2277 107 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 167 279 (accept_3_4 106 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 167 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 105 167
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 167 279 (accept_3_4 103 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 167 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 102 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 167 279 (Polychromatic418967fa.accept_15_11_2_9_1_1480 101 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 167 279 (accept_3_4 100 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 167 279 (Polychromatic418967fa.accept_13_8_11_6_1_1035 99 167
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 167 279 (accept_3_4 97 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 167 279 (Polychromatic418967fa.accept_13_5_11_6_1_505 96 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 167 279 (Polychromatic418967fa.accept_13_4_11_6_1_1033 95 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 167 279 (accept_3_4 94 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 167
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 167 279 (accept_3_4 91 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 167 279 (Polychromatic418967fa.accept_19_14_15_13_1_4898 90 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 279 (Polychromatic418967fa.accept_17_4_14_7_1_4965 89 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 167 279 (accept_3_4 88 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 167 279
  (Polychromatic418967fa.accept_18_15_5_9_1_5529 87 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 167 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 279 (accept_3_4 85 167 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 167 279 (Polychromatic418967fa.accept_18_12_5_9_1_6896 84 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 279
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 167 279 (accept_3_4 82 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 279 (accept_3_4 79 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 78 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 279
  (Polychromatic418967fa.accept_20_17_7_19_1_13006 77 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 167 279 (accept_3_4 76 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 167 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 75 167 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 279 (accept_3_4 73 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 279 (Polychromatic418967fa.accept_10_2_7_9_1_783
  72 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 279
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 71 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 279 (accept_3_4 70 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 279 (accept_3_4 67 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 279 (Polychromatic418967fa.accept_18_12_5_9_1_6896 66 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 279
  (Polychromatic418967fa.accept_21_2_20_6_1_2277 65 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 279 (accept_3_4 64 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 279 (Polychromatic418967fa.accept_19_6_15_13_1_3498 63 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 279 (accept_3_4 61 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 279 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 279
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 59 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 279 (accept_3_4 58 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 279 (accept_3_4 55 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 279 (Polychromatic418967fa.accept_19_16_15_13_1_1335 54 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 279
  (Polychromatic418967fa.accept_11_9_2_4_1_707 53 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 279 (accept_3_4 52 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 279 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 279 (accept_3_4 49 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 279
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 279 (accept_3_4 46 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 279 (accept_3_4 43 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 279
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 279 (accept_3_4 40 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 279 (accept_3_4 37 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 279 (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 279
  (Polychromatic418967fa.accept_19_16_15_13_1_1335 35 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 167 279 (accept_3_4 34 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 167 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 279 (accept_3_4 31 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 279
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 167 279 (Polychromatic418967fa.accept_22_7_13_15_1_9473 29 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 279 (accept_3_4 28 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 279 (Polychromatic418967fa.accept_17_10_14_7_1_2679 27 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 279 (accept_3_4 25 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 279 (Polychromatic418967fa.accept_21_3_20_6_1_5126 24 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 279 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 279 (accept_3_4 22 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 167
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 279 (accept_3_4 19 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 279 (accept_3_4 16 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 279 (Polychromatic418967fa.accept_18_15_5_9_1_5529 15 167
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 279 (accept_3_4 13 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 279 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 279 (accept_3_4 10 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 167 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 279 (accept_3_4 7 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 279 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 279 (accept_3_4 4 167 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 279 (Polychromatic418967fa.accept_21_3_20_6_1_5126 3 167 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 279 (accept_3_4 1 167 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 166 279 (Eq.refl Bool.true) (allA_succ_of_accept 113 166 279 (accept_3_5 113 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 166 279 (Polychromatic418967fa.accept_15_7_1_9_1_1500 112 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 166 279
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 111 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 166 279 (accept_3_5 110 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 166 279 (Polychromatic418967fa.accept_13_4_10_6_1_989 108 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 166 279 (accept_3_5 107 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 166 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 106 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 166 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 166 279 (accept_3_5 104 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 166 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 166 279 (accept_3_5 101 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 166 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 100
  166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 166 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 166 279 (accept_3_5 98 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 166 279 (Polychromatic418967fa.accept_11_8_1_4_1_2318 96 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 166 279 (accept_3_5 95 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 166 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 94 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 166 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 166 279 (accept_3_5 92 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 166 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 166 279 (accept_3_5 89 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 166 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 166 279
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 87 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 166 279 (accept_3_5 86 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 166 279 (Polychromatic418967fa.accept_18_12_4_9_1_5452 84 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 166 279 (accept_3_5 83 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 166 279 (Polychromatic418967fa.accept_13_4_10_6_1_989 82 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 166 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 166 279 (accept_3_5 80 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 166 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 166 279 (accept_3_5 77 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 166 279 (Polychromatic418967fa.accept_14_6_12_13_1_3180 76 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 166 279
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 75 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 166 279 (accept_3_5 74 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 166 279 (Polychromatic418967fa.accept_19_15_14_13_1_2343 72 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 166 279 (accept_3_5 71 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 166 279 (Polychromatic418967fa.accept_13_5_10_6_1_2361 70 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 166 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 166 279 (accept_3_5 68 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 166 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 166 279 (accept_3_5 65 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 166 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 166 279
  (Polychromatic418967fa.accept_10_3_6_9_1_779 63 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 166 279 (accept_3_5 62 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 166 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 166 279 (accept_3_5 59 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 166 279 (Polychromatic418967fa.accept_19_1_14_13_1_6294 58 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 166 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 166 279 (accept_3_5 56 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 166 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 166 279 (accept_3_5 53 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 166 279 (Polychromatic418967fa.accept_11_8_1_4_1_2318 52 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 166 279
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 166 279 (accept_3_5 50 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 279 (accept_3_5 47 166
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 166 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 279 (accept_3_5 44 166 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 279 (accept_3_5 41 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 279 (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 279 (accept_3_5 38 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 279 (accept_3_5 35 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 279 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 279 (accept_3_5 32 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 279
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 279 (accept_3_5 29 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 279 (Polychromatic418967fa.accept_19_8_14_13_1_11837 27 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 279 (accept_3_5 26 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 279
  (Polychromatic418967fa.accept_19_5_14_13_1_7816 24 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 166 279 (accept_3_5 23 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 166 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 166 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 279 (accept_3_5 20 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 279 (accept_3_5 17 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 279 (accept_3_5 14 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 279
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 166 279 (accept_3_5 11 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 166 279 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 166 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 279 (accept_3_5 8 166 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 279 (accept_3_5 5 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 166 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 279 (accept_3_5 2 166 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 165 279 (Eq.refl Bool.true) (allA_succ_of_gcd 114 165 279 3 38 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 165 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 113 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 165 279 (Polychromatic418967fa.accept_21_7_18_6_1_9797 112 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 165 279 3 37 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 165 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 109 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 165 279 3 36 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 165 279 (Polychromatic418967fa.accept_7_2_4_6_1_166
  107 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 165 279 3 35 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 165 279 (Polychromatic418967fa.accept_10_4_5_9_1_1231 104 165 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 103 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 165 279 3 34 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 165 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 165 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 165 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 100 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 165 279 3 33 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  97 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 165 279 3 32 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 165 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 95 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 165 279 3 31 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 165 279 (Polychromatic418967fa.accept_13_1_9_6_1_146
  92 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 91 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 165 279 3 30 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 165 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 279
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 88 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 165 279 3 29 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  85 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 165 279 3 28 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 165 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 83 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 165 279 3 27 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 165 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 80
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 165 279 3 26 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 165 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 279 (Polychromatic418967fa.accept_10_6_5_9_1_1233
  76 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 165 279 3 25 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 165 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 165 279 3 24 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 165 279 (Polychromatic418967fa.accept_10_1_5_9_1_157
  71 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 165 279 3 23 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 165 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 279 (Polychromatic418967fa.accept_12_7_9_3_1_767
  67 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 279 3 22 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 279 (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 279 3 21 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 279 3 20 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 279 3 19 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 279
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 279 3 18 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 165 279 3 17 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  49 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 165 279 3 16 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 165 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 279 3 15 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 44
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 279 3 14 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 279 (Polychromatic418967fa.accept_7_5_4_6_1_167
  40 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 279 3 13 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 279 3 12 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 165 279 3 11 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 165 279 (Polychromatic418967fa.accept_18_14_3_9_1_4234 32 165 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 165 279 3 10 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 165 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 165 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 279 (Polychromatic418967fa.accept_13_2_9_6_1_501
  28 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 279 3 9 55 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 279 3 8 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 279 3 7 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 279 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 165 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 279 3 6 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 279 3 5 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 279 3 4 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 279 3 3 55 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 279
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 279 3 2 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 165 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 279
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 165 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 279 3 1 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 165 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 164 279 (Eq.refl Bool.true) (allA_succ_of_accept 115 164 279 (accept_3_4 115 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 113 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 164 279 (accept_3_4 112 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 164 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 111 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 164 279 (Polychromatic418967fa.accept_15_5_14_9_1_274 110 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 164 279 (accept_3_4 109 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 164 279
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 108 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 164 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 107 164 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 164 279 (accept_3_4 106 164 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 164 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 105 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 164 279
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 104 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 164 279 (accept_3_4 103 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 164 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 164 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 101 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 164 279 (accept_3_4 100 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 164 279
  (Polychromatic418967fa.accept_8_3_4_7_1_475 99 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 164 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 164 279 (accept_3_4 97 164 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 164 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 96 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 164 279 (accept_3_4 94 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 164 279 (Polychromatic418967fa.accept_13_1_8_6_1_1016 92 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 164 279 (accept_3_4 91 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 164 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 164 279 (accept_3_4 88 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 164 279 (Polychromatic418967fa.accept_14_3_10_13_1_339 87 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 164 279 (accept_3_4 85 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 164 279 (Polychromatic418967fa.accept_26_6_8_19_1_17103 84 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 164 279 (accept_3_4 82 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 164 279 (Polychromatic418967fa.accept_13_2_8_6_1_2390 80 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 164 279 (accept_3_4 79 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 164 279 (accept_3_4 76 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 164 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 164 279 (accept_3_4 73 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 164 279 (accept_3_4 70 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 164 279 (Polychromatic418967fa.accept_17_1_11_7_1_4962 69 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 164 279 (accept_3_4 67 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 164 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 164 279 (accept_3_4 64 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 164 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 164 279 (Polychromatic418967fa.accept_16_14_4_7_1_2380 62 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 164 279 (accept_3_4 61 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 164 279 (accept_3_4 58 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 164 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 57 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 164 279 (Polychromatic418967fa.accept_16_8_4_7_1_3390 56 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 164 279 (accept_3_4 55 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 164 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 164 279 (accept_3_4 52 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 164 279 (Polychromatic418967fa.accept_13_11_8_6_1_1023 50 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 279 (accept_3_4 49 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 164 279 (accept_3_4 46 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 164 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 279 (accept_3_4 43 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 164 279 (accept_3_4 40 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 279 (accept_3_4 37 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 164 279 (accept_3_4 34 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 164 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 279 (accept_3_4 31 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 279 (accept_3_4 28 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 279 (Polychromatic418967fa.accept_22_4_10_15_1_17137 26 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 279 (accept_3_4 25 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 279 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 279 (accept_3_4 22 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 279 (Polychromatic418967fa.accept_15_5_14_9_1_274 20 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 279 (accept_3_4 19 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 164 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 279 (accept_3_4 16 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 279 (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 279 (accept_3_4 13 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 164
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 279 (accept_3_4 10 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 279 (accept_3_4 7 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 164 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 279 (accept_3_4 4 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 164 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 279 (accept_3_4 1 164 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 163 279 (Eq.refl Bool.true) (allA_succ_of_accept 116 163 279 (accept_3_5 116 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 115 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 163 279
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 114 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 163 279 (accept_3_5 113 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 163 279 (Polychromatic418967fa.accept_16_15_3_7_1_3389 111 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 163 279 (accept_3_5 110 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 163 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 109 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 163 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 163 279 (accept_3_5 107 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 105 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 163 279 (accept_3_5 104 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 163 279 (Polychromatic418967fa.accept_13_12_7_6_1_1015 103
  163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 163 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 163 279 (accept_3_5 101 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 163 279 (accept_3_5 98 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 163 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 97 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 163 279
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 96 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 163 279 (accept_3_5 95 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 93 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 163 279 (accept_3_5 92 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 163 279 (Polychromatic418967fa.accept_16_11_3_7_1_2375 91 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 163 279
  (Polychromatic418967fa.accept_11_2_9_4_1_310 90 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 163 279 (accept_3_5 89 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 163 279 (accept_3_5 86 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 163 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 163 279 (accept_3_5 83 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 163 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 163 279 (accept_3_5 80 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 163 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 79 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 163 279 (accept_3_5 77 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 163 279 (Polychromatic418967fa.accept_16_11_3_7_1_2375 75 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 279 (accept_3_5 74 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 279
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 72 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 163 279 (accept_3_5 71 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 279 (accept_3_5 68 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 163 279 (accept_3_5 65 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 163 279 (Polychromatic418967fa.accept_15_3_13_9_1_3196 63 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 279 (accept_3_5 62 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 279 (Polychromatic418967fa.accept_13_9_7_6_1_1673 61 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 279 (accept_3_5 59 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 279 (accept_3_5 56 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 279 (Polychromatic418967fa.accept_19_17_11_13_1_4840 55 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 279
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 279 (accept_3_5 53 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 279 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 279 (accept_3_5 50 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 279 (Polychromatic418967fa.accept_15_4_13_9_1_3197 49 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 279
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 279 (accept_3_5 47 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 279 (accept_3_5 44 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 279
  (Polychromatic418967fa.accept_16_10_3_7_1_8094 42 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 279 (accept_3_5 41 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 279 (accept_3_5 38 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 37 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 279 (accept_3_5 35 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 279 (accept_3_5 32 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 279
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 30 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 279 (accept_3_5 29 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 279 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 279 (accept_3_5 26 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 279 (accept_3_5 23 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 279 (accept_3_5 20 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 279 (Polychromatic418967fa.accept_15_4_13_9_1_3197 19 163
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 279 (accept_3_5 17 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 279 (accept_3_5 14 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 279 (accept_3_5 11 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 279 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 279 (accept_3_5 8 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 279
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 279 (accept_3_5 5 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 279 (accept_3_5 2 163 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 162 279 (Eq.refl Bool.true) (allA_succ_of_gcd 117 162 279 9 13 18 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 162 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 116 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 162 279 (Polychromatic418967fa.accept_15_10_12_9_1_776 115 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 279 3 38 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 162 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 112 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 162 279 3 37 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 162 279 (Polychromatic418967fa.accept_7_5_1_6_1_163
  110 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 162 279 9 12 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 162 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 162 279
  (Polychromatic418967fa.accept_11_7_8_4_1_718 106 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 162 279 3 35 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 162 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 104 162 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 162 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 162 279 3 34 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173
  100 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 162 279 9 11 18 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 162 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 98 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 279 3 32 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 279 (Polychromatic418967fa.accept_11_7_8_4_1_718
  95 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 162 279
  (Polychromatic418967fa.accept_12_10_6_3_1_786 94 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 162 279 3 31 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 162 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 92 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 162 279 (Polychromatic418967fa.accept_10_1_2_9_1_152
  91 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 162 279 9 10 18 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 162 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 162 279 3 29 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 86
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 85 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 279 3 28 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 279 (Polychromatic418967fa.accept_17_15_9_7_1_3816 83 162 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 162 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 82 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 162 279 9 9 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 162 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 80 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 162 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 162 279 3 26 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 162 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 162 279 3 25 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 162 279 (Polychromatic418967fa.accept_12_2_6_3_1_331
  74 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 279 9 8 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 162 279 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 162
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 162 279 3 23 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 162 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 162 279 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 162 279 3 22 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 162 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 162 279 9 7 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 162 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 62 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 162 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 162 279 3 20 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 162 279
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 59 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 162 279 3 19 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 162 279
  (Polychromatic418967fa.accept_11_1_8_4_1_717 56 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 162 279 (Polychromatic418967fa.accept_15_10_12_9_1_776 55 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 162 279 9 6 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 162 279 3 17 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 162 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 279 3 16 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 162 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 162 279 9 5 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 279
  (Polychromatic418967fa.accept_16_11_2_7_1_3374 43 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 279 3 14 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 279 (Polychromatic418967fa.accept_7_5_1_6_1_163
  40 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 162 279 3 13 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 162 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 279 9 4 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 279 (Polychromatic418967fa.accept_14_7_8_13_1_3161
  35 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 279
  (Polychromatic418967fa.accept_11_1_8_4_1_717 34 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 162 279 3 11 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 162 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 162 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 279 (Polychromatic418967fa.accept_10_1_2_9_1_152
  31 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 162 279 3 10 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 162 279 9 3 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 162 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 26
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 279 3 8 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 162
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 162 279 3 7 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 162 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 279 9 2 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 162 279 3 5 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 162 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 279 3 4 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 279
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 279 9 1 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 162 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 279
  (Polychromatic418967fa.accept_10_7_2_9_1_775 7 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 279 3 2 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 162 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 279 3 1 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 162 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 161 279 (Eq.refl Bool.true) (allA_succ_of_accept 118 161 279 (accept_3_4 118 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 117 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 161 279 (accept_3_4 115 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 161 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 113 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 161 279 (accept_3_4 112 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 161 279 (Polychromatic418967fa.accept_15_6_11_9_1_3215 111
  161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 161 279 (accept_3_4 109 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 161 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 108 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 161 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 107 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 161 279 (accept_3_4 106 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 105 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 161 279 (accept_3_4 103 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 161 279 (Polychromatic418967fa.accept_13_10_5_6_1_1671 101 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 279 (accept_3_4 100 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 99 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 279 (accept_3_4 97 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 96 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 95 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 279 (accept_3_4 94 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 279 (accept_3_4 91 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 279 (Polychromatic418967fa.accept_13_11_5_6_1_519 89 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 279 (accept_3_4 88 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 279 (Polychromatic418967fa.accept_18_15_17_9_1_4200 87 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 279 (accept_3_4 85 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 279 (Polychromatic418967fa.accept_17_16_8_7_1_4983 84 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 279 (Polychromatic418967fa.accept_19_7_9_13_1_4836 83 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 279 (accept_3_4 82 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 279 (accept_3_4 79 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 279 (Polychromatic418967fa.accept_13_12_5_6_1_1050 77 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 279 (accept_3_4 76 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 279 (accept_3_4 73 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 71 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 279 (accept_3_4 70 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 279 (accept_3_4 67 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 65 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 279 (accept_3_4 64 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 279 (accept_3_4 61 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 279 (Polychromatic418967fa.accept_19_3_9_13_1_15893 60 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 279 (Polychromatic418967fa.accept_27_5_26_9_1_11486 59 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 279 (accept_3_4 58 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 279 (accept_3_4 55 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 279 (Polychromatic418967fa.accept_13_1_5_6_1_1048 53 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 279 (accept_3_4 52 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 279 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 279 (accept_3_4 49 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 279 (accept_3_4 46 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 279 (accept_3_4 43 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 279 (accept_3_4 40 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 279 (Polychromatic418967fa.accept_21_18_14_6_1_8278 39 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 279 (accept_3_4 37 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 279 (accept_3_4 34 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 279 (accept_3_4 31 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 279 (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 279 (accept_3_4 28 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 279 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 279 (accept_3_4 25 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 279 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 279 (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 279 (accept_3_4 22 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 279 (accept_3_4 19 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 279 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 279 (accept_3_4 16 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 161
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 279 (accept_3_4 13 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 279 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 279 (accept_3_4 10 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 161 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 279 (accept_3_4 7 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 161 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 279 (accept_3_4 4 161 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 161 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 279 (accept_3_4 1 161 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 160 279 (Eq.refl Bool.true) (allA_succ_of_accept 119 160 279 (accept_3_5 119 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 160 279 (Polychromatic418967fa.accept_19_4_8_13_1_7802 118
  160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 160 279
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 117 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 160 279 (accept_3_5 116 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 160 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 114 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 160 279 (accept_3_5 113 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 160 279
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 112 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 160 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 111 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 160 279 (accept_3_5 110 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 109 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 109 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 160 279
  (Polychromatic418967fa.accept_15_3_10_9_1_769 108 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 160 279 (accept_3_5 107 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 160 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 106 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 160 279 (Polychromatic418967fa.accept_14_7_6_13_1_4111 105 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 160 279 (accept_3_5 104 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 160 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 102 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 160 279 (accept_3_5 101 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 160 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 100 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 160 279 (Polychromatic418967fa.accept_19_4_8_13_1_7802 99 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 160 279 (accept_3_5 98 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 160 279
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 96 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 160 279 (accept_3_5 95 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 160 279 (Polychromatic418967fa.accept_15_4_10_9_1_4298 94 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 160 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 93 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 160 279 (accept_3_5 92 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 160 279
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 90 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 160 279 (accept_3_5 89 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 160 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 88 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 160 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 87 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 160 279 (accept_3_5 86 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 160 279
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 84 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 160 279 (accept_3_5 83 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 160 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 82 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 160 279
  (Polychromatic418967fa.accept_19_5_8_13_1_9161 81 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 160 279 (accept_3_5 80 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 160 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 160 279 (accept_3_5 77 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 160 279 (Polychromatic418967fa.accept_13_11_4_6_1_1006 76 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 160 279
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 75 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 160 279 (accept_3_5 74 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 160 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 160 279 (accept_3_5 71 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 160 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371 70 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 160 279
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 69 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 160 279 (accept_3_5 68 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 160 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 160 279 (accept_3_5 65 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 160 279
  (Polychromatic418967fa.accept_15_4_10_9_1_4298 64 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 160 279 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 279 (accept_3_5 62 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 160 279
  (Polychromatic418967fa.accept_19_3_8_13_1_13229 60 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 160 279 (accept_3_5 59 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 160 279 (Polychromatic418967fa.accept_19_1_8_13_1_4875 58 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 279 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 160 279 (accept_3_5 56 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 160 279
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 160 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 279 (accept_3_5 53 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 160 279 (Polychromatic418967fa.accept_19_14_8_13_1_4834 52 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 279
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 160 279 (accept_3_5 50 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 48 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 279 (accept_3_5 47 160
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 279
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 160 279 (Polychromatic418967fa.accept_21_3_13_6_1_11322 45 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 279 (accept_3_5 44 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 279 (accept_3_5 41 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 279 (Polychromatic418967fa.accept_19_1_8_13_1_4875 39 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 279 (accept_3_5 38 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 279
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 279 (accept_3_5 35 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 279 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 279 (accept_3_5 32 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 279 (accept_3_5 29 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 279 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 279 (accept_3_5 26 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 279
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 279 (accept_3_5 23 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 279 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 279 (accept_3_5 20 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 279 (accept_3_5 17 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 279 (Polychromatic418967fa.accept_15_1_10_9_1_1495 16 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 279 (accept_3_5 14 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 279
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 160 279 (accept_3_5 11 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 160 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 160 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 279 (accept_3_5 8 160 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 279 (accept_3_5 5 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 279 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 160 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 279 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 279 (accept_3_5 2 160 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 159 279 (Eq.refl Bool.true) (allA_succ_of_gcd 120 159 279 3 40 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 159 279
  (Polychromatic418967fa.accept_18_11_15_9_1_360 119 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 159 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 118 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 159 279 3 39 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 159 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 116 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 159 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 115 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 159 279 3 38 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 159 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 113 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 159 279 (Polychromatic418967fa.accept_18_4_15_9_1_6882 112 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 159 279 3 37 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 159 279
  (Polychromatic418967fa.accept_16_14_15_7_1_5655 110 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 159 279 3 36 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 159 279
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 107 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 106 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 159 279 3 35 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 159 279
  (Polychromatic418967fa.accept_14_6_5_13_1_367 104 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 159 279 (Polychromatic418967fa.accept_21_19_12_6_1_6689 103 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 159 279 3 34 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 159 279
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 101 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 159 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 100 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 159 279 3 33 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 159 279
  (Polychromatic418967fa.accept_11_10_5_4_1_711 98 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 159 279 (Polychromatic418967fa.accept_19_2_7_13_1_2337 97 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 159 279 3 32 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 95
  159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 279
  (Polychromatic418967fa.accept_16_14_15_7_1_5655 94 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 159 279 3 31 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 279
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 91 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 159 279 3 30 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 159 279 (Polychromatic418967fa.accept_18_17_15_9_1_5542 89 159 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 88 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 159 279 3 29 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 159 279 (Polychromatic418967fa.accept_16_6_15_7_1_1510 86 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 159 279 3 28 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 159 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 83 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 279
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 82 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 159 279 3 27 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 159 279 (Polychromatic418967fa.accept_19_4_7_13_1_3480 80 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 279
  (Polychromatic418967fa.accept_13_1_3_6_1_158 79 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 159 279 3 26 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 159 279 (Polychromatic418967fa.accept_18_5_15_9_1_1919 77 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 279
  (Polychromatic418967fa.accept_11_10_5_4_1_711 76 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 279 3 25 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 279
  (Polychromatic418967fa.accept_21_10_12_6_1_5124 73 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 159 279 3 24 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 279
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 159 279 3 23 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 159 279 (Polychromatic418967fa.accept_19_11_7_13_1_9129 68 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 159 279 3 22 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 159 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 65 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 64 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 159 279 3 21 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 159 279 (Polychromatic418967fa.accept_13_10_3_6_1_1003 62 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 279
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 61 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 159 279 3 20 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 159 279 (Polychromatic418967fa.accept_16_11_15_7_1_5654 59 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 279
  (Polychromatic418967fa.accept_18_4_15_9_1_6882 58 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 279 3 19 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 279 (Polychromatic418967fa.accept_16_8_15_7_1_5658 56 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 279
  (Polychromatic418967fa.accept_19_17_7_13_1_4833 55 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 159 279 3 18 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 279
  (Polychromatic418967fa.accept_18_16_15_9_1_6852 52 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 159 279 3 17 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 279
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 279 3 16 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 279 (Polychromatic418967fa.accept_17_13_6_7_1_4999 47 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 279 3 15 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 44 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 279 3 14 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 279 (Polychromatic418967fa.accept_18_5_15_9_1_1919 41 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 279
  (Polychromatic418967fa.accept_13_1_3_6_1_158 40 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 279 3 13 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 279 (Polychromatic418967fa.accept_16_6_15_7_1_1510 38 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 279
  (Polychromatic418967fa.accept_21_16_12_6_1_8274 37 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 159 279 3 12 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 159 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 159 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 279
  (Polychromatic418967fa.accept_14_6_5_13_1_367 34 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 279 3 11 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278
  31 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 279 3 10 53 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 279 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 279 3 9 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 279
  (Polychromatic418967fa.accept_21_5_12_6_1_11321 26 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 279 3 8 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 279
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 279 3 7 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 279 (Polychromatic418967fa.accept_14_6_5_13_1_367
  20 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 279
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 279 3 6 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 279 (Polychromatic418967fa.accept_18_17_15_9_1_5542 17 159 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 279
  (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 279 3 5 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 279 (Polychromatic418967fa.accept_17_13_6_7_1_4999 13 159
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 279 3 4 53 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 279 3 3 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 279
  (Polychromatic418967fa.accept_21_7_12_6_1_3624 7 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 279 3 2 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 279 3 1 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 279
  (Polychromatic418967fa.accept_19_2_7_13_1_2337 2 159 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 158 279 (Eq.refl Bool.true) (allA_succ_of_accept 121 158 279 (accept_3_4 121 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 158 279 (Polychromatic418967fa.accept_21_15_11_6_1_5121 120
  158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 158 279 (accept_3_4 118 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 158 279 (Polychromatic418967fa.accept_13_12_2_6_1_2396 116 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 158 279 (accept_3_4 115 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 158 279 (accept_3_4 112 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 158 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 111 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 110 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 158 279 (accept_3_4 109 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 158 279 (accept_3_4 106 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 158 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 104 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 158 279 (accept_3_4 103 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 102 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 158 279 (accept_3_4 100 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 158 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385 99 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 158 279 (Polychromatic418967fa.accept_21_14_11_6_1_8305 98 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 158 279 (accept_3_4 97 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 158 279 (accept_3_4 94 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 158 279 (Polychromatic418967fa.accept_13_1_2_6_1_515 92 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 158 279 (accept_3_4 91 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 158 279 (accept_3_4 88 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 158 279 (accept_3_4 85 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 158 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 158 279 (accept_3_4 82 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 158 279 (accept_3_4 79 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 158 279 (accept_3_4 76 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 158 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 74 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 279 (accept_3_4 73 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 158 279 (accept_3_4 70 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 279 (accept_3_4 67 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 158 279 (accept_3_4 64 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 158 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 63 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 158 279 (Polychromatic418967fa.accept_13_10_2_6_1_1044 62 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 279 (accept_3_4 61 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 158 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385 60 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 158 279 (accept_3_4 58 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 158 279 (Polychromatic418967fa.accept_13_4_2_6_1_1043 56 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 158 279 (accept_3_4 55 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 158 279 (accept_3_4 52 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 158 279 (Polychromatic418967fa.accept_19_12_6_13_1_2305 50 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 158 279 (accept_3_4 49 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 158 279 (Polychromatic418967fa.accept_13_9_2_6_1_514 48 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 158 279 (accept_3_4 46 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 279 (accept_3_4 43 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 158 279 (accept_3_4 40 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 158 279 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 279 (accept_3_4 37 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 279 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 158 279 (accept_3_4 34 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 158 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 279 (accept_3_4 31 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 279 (accept_3_4 28 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 279 (accept_3_4 25 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 158 279 (accept_3_4 22 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 279 (Polychromatic418967fa.accept_16_4_14_7_1_5641 20 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 279 (accept_3_4 19 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 158
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 279 (accept_3_4 16 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 279 (Polychromatic418967fa.accept_16_15_14_7_1_10555 15 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 279 (accept_3_4 13 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 158 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 279 (accept_3_4 10 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 279 (accept_3_4 7 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 158 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 279 (accept_3_4 4 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 279 (accept_3_4 1 158 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 157 279 (Eq.refl Bool.true) (allA_succ_of_accept 122 157 279 (accept_3_5 122 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 157 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 121 157 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 157 279
  (Polychromatic418967fa.accept_13_3_1_6_1_509 120 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 157 279 (accept_3_5 119 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 157 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 117 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 157 279 (accept_3_5 116 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 157 279 (Polychromatic418967fa.accept_20_15_17_19_1_10076 115
  157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 157 279 (accept_3_5 113 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 157 279 (Polychromatic418967fa.accept_13_7_1_6_1_3287 111 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 157 279 (accept_3_5 110 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 157 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 109 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 157 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 108 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 157 279 (accept_3_5 107 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 105 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 157 279 (accept_3_5 104 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 157 279 (Polychromatic418967fa.accept_15_13_7_9_1_3210 103
  157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 157 279 (accept_3_5 101 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 157 279 (Polychromatic418967fa.accept_13_8_1_6_1_997 99 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 157 279 (accept_3_5 98 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 157 279 (Polychromatic418967fa.accept_17_12_4_7_1_6257 97 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 157 279
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 96 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 157 279 (accept_3_5 95 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 157 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 157 279 (accept_3_5 92 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 157 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 91 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 157 279 (accept_3_5 89 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 157 279 (Polychromatic418967fa.accept_13_9_1_6_1_510 87 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 279 (accept_3_5 86 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 279 (Polychromatic418967fa.accept_13_7_1_6_1_3287 85 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 279
  (Polychromatic418967fa.accept_11_7_3_4_1_729 84 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 279 (accept_3_5 83 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 279 (accept_3_5 80 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 279 (accept_3_5 77 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 279 (Polychromatic418967fa.accept_18_3_13_9_1_4260 75 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 279 (accept_3_5 74 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 73 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 279 (accept_3_5 71 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 279 (accept_3_5 68 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 157 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 279 (accept_3_5 65 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 279 (Polychromatic418967fa.accept_17_12_4_7_1_6257 63 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 279 (accept_3_5 62 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 279 (Polychromatic418967fa.accept_13_9_1_6_1_510 61 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 279 (accept_3_5 59 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 279 (accept_3_5 56 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 279 (Polychromatic418967fa.accept_13_3_1_6_1_509 55 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 279 (accept_3_5 53 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 279 (accept_3_5 50 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 279 (Polychromatic418967fa.accept_19_11_5_13_1_11849 49 157 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 279 (accept_3_5 47 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 279 (accept_3_5 44 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 279 (Polychromatic418967fa.accept_15_13_7_9_1_3210 43 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 279 (accept_3_5 41 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 279 (accept_3_5 38 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 279
  (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 279 (accept_3_5 35 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 279 (accept_3_5 32 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 279 (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 279 (accept_3_5 29 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 279 (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 279 (accept_3_5 26 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 279
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 157 279 (accept_3_5 23 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 279 (accept_3_5 20 157
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 279
  (Polychromatic418967fa.accept_22_19_3_15_1_14096 19 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 279 (accept_3_5 17 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 279
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 279 (accept_3_5 14 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 279 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 279 (accept_3_5 11 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 279 (accept_3_5 8 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 279 (accept_3_5 5 157 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 279
  (Polychromatic418967fa.accept_13_3_1_6_1_509 3 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 279 (accept_3_5 2 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 157 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 156 279 (Eq.refl Bool.true) (allA_succ_of_gcd 123 156 279 3 41 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 156 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 122 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 156 279 (Polychromatic418967fa.accept_15_1_6_9_1_254 121 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 156 279 3 40 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 156 279 (Polychromatic418967fa.accept_11_9_2_4_1_707
  119 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 156 279
  (Polychromatic418967fa.accept_17_16_3_7_1_5028 118 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 117 156 279 3 39 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 116 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 116 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 156 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 115 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 156 279 3 38 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 156 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 156 279
  (Polychromatic418967fa.accept_17_10_3_7_1_1679 112 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 156 279 3 37 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 156 279 (Polychromatic418967fa.accept_19_15_4_13_1_4939 110 156 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 156 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 109 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 156 279 3 36 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 156 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 107 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 106 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 156 279 3 35 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 156 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274 104 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 156 279
  (Polychromatic418967fa.accept_10_3_6_9_1_779 103 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 156 279 3 34 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 156 279
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 100 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 156 279 3 33 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 156 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 98 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 156 279
  (Polychromatic418967fa.accept_11_9_2_4_1_707 97 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 279 3 32 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 94
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 156 279 3 31 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 156 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 156 279 3 30 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  89 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 156 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 88 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 156 279 3 29 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 156 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 86 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 156 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 85
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 156 279 3 28 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 156 279
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 156 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 82 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 156 279 3 27 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 156 279
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 79 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 279 3 26 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 279 (Polychromatic418967fa.accept_18_5_12_9_1_6871 77 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 156 279
  (Polychromatic418967fa.accept_15_1_6_9_1_254 76 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 156 279 3 25 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 73
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 279 3 24 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 156 279 (Polychromatic418967fa.accept_18_16_12_9_1_5504 70 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 156 279 3 23 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 156 279
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 68 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 279 3 22 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 279 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  65 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 156 279 3 21 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 156 279 (Polychromatic418967fa.accept_21_20_9_6_1_11288 62 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 279
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 61 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 279 3 20 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 279
  (Polychromatic418967fa.accept_18_4_12_9_1_2011 58 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 156 279 3 19 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 156 279 (Polychromatic418967fa.accept_15_11_6_9_1_3236 56 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 279
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 55 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 279 3 18 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 52
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 156 279 3 17 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 279 (Polychromatic418967fa.accept_15_4_6_9_1_2269 49 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 279 3 16 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 279 (Polychromatic418967fa.accept_18_11_12_9_1_992
  47 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 156 279 3 15 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 156 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274 44 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 279 3 14 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 279 (Polychromatic418967fa.accept_15_11_6_9_1_3236 41 156 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 279
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 40 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 156 279 3 13 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 279
  (Polychromatic418967fa.accept_16_5_12_7_1_3411 37 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 279 3 12 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 279 (Polychromatic418967fa.accept_15_4_6_9_1_2269
  34 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 156 279 3 11 52 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 156 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 279 3 10 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 279
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 156 279 3 9 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 156 279 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 279 3 8 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 279
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 156 279 3 7 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 279 (Polychromatic418967fa.accept_11_9_2_4_1_707
  20 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 279
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 279 3 6 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 279 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 156
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 279 3 5 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 279
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 279 3 4 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 156 279 3 3 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 156 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 279 (Polychromatic418967fa.accept_19_7_4_13_1_6319 7 156
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 279 3 2 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 279
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 156 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 279 3 1 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 156 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 155 279 (Eq.refl Bool.true) (allA_succ_of_gcd 124 155 279 31 4 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 155 279
  (Polychromatic418967fa.accept_15_3_5_9_1_764 123 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 122 155 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 155 279 (accept_3_4 121 155 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 155 279 (Polychromatic418967fa.accept_18_12_11_9_1_4257 120 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 155 279
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 119 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 155 279 (accept_3_4 118 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 155 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 116 155
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 279 (accept_3_4 115 155
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 114 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 155 279 (Polychromatic418967fa.accept_22_3_1_15_1_7876 113 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 155 279 (accept_3_4 112 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 155 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 111 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 155 279 (accept_3_4 109 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 155 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 155 279 (accept_3_4 106 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 155 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 105 155
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 155 279 (accept_3_4 103 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 155 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 102 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 101 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 155 279 (accept_3_4 100 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 155 279 (Polychromatic418967fa.accept_16_3_11_7_1_770
  99 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 155 279 (accept_3_4 97 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 155 279 (Polychromatic418967fa.accept_16_15_11_7_1_6951 95 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 155 279 (accept_3_4 94 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 155 279 31 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 279 (accept_3_4 91 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 279
  (Polychromatic418967fa.accept_20_10_15_19_1_12983 90 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 279 (accept_3_4 88 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 155 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 87 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 155 279 (accept_3_4 85 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 155 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 155 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 83 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 279 (accept_3_4 82 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 155
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 279 (accept_3_4 79 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 78 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 279 (Polychromatic418967fa.accept_14_7_1_13_1_357 77 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 279 (accept_3_4 76 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 279 (accept_3_4 73 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 71 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 279 (accept_3_4 70 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 155
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 279 (accept_3_4 67 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 279 (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 279 (accept_3_4 64 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 279 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 155 279 31 2 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 155 279 (accept_3_4 61 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 279
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 59 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 279 (accept_3_4 58 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 279 (accept_3_4 55 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 279
  (Polychromatic418967fa.accept_16_5_11_7_1_5635 53 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 279 (accept_3_4 52 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 279 (accept_3_4 49 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 48 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 279 (accept_3_4 46 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 279 (accept_3_4 43 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 279 (accept_3_4 40 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 279 (Polychromatic418967fa.accept_27_12_20_9_1_17136 39 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 279 (accept_3_4 37 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 279
  (Polychromatic418967fa.accept_14_7_1_13_1_357 35 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 279 (accept_3_4 34 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 31 155 279 31 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 30 155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 279
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 29 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 279 (accept_3_4 28 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 279 (accept_3_4 25 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 279 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 279 (accept_3_4 22 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 279 (accept_3_4 19 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 279
  (Polychromatic418967fa.accept_20_17_15_19_1_12975 17 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 155 279 (accept_3_4 16 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 155 279 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 155 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 279 (accept_3_4 13 155 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 279 (Polychromatic418967fa.accept_7_5_1_6_1_163
  12 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 279 (accept_3_4 10 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 279 (accept_3_4 7 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 279 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 155 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 279 (accept_3_4 4 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 155 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 279 (accept_3_4 1 155 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 154 279 (Eq.refl Bool.true) (allA_succ_of_accept 125 154 279 (accept_3_5 125 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 154 279 (Polychromatic418967fa.accept_19_10_2_13_1_9183 124
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 154 279
  (Polychromatic418967fa.accept_10_3_4_9_1_15 123 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 154 279 (accept_3_5 122 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 154 279 (Polychromatic418967fa.accept_18_12_10_9_1_5497 120 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 154 279 (accept_3_5 119 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 118 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 154 279 (accept_3_5 116 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 114 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 154 279 (accept_3_5 113 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 154 279 (Polychromatic418967fa.accept_13_8_11_6_1_1035 112
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 154 279
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 111 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 154 279 (accept_3_5 110 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 108 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 154 279 (accept_3_5 107 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 154 279 (Polychromatic418967fa.accept_19_11_2_13_1_4907 106
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 154 279 (accept_3_5 104 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 102 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 154 279 (accept_3_5 101 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 154 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 100
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 154 279
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 99 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 154 279 (accept_3_5 98 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 154 279 (Polychromatic418967fa.accept_13_5_11_6_1_505 96 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 154 279 (accept_3_5 95 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 154 279 (Polychromatic418967fa.accept_16_14_10_7_1_2363 94 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 154 279 (accept_3_5 92 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 154 279 (accept_3_5 89 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 154 279
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 87 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 154 279 (accept_3_5 86 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 154 279 (Polychromatic418967fa.accept_18_12_10_9_1_5497 84 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 154 279 (accept_3_5 83 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 154 279 (Polychromatic418967fa.accept_13_4_11_6_1_1033 82 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 154 279 (accept_3_5 80 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 154 279 (accept_3_5 77 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 154 279 (Polychromatic418967fa.accept_17_8_1_7_1_7488 76 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 154 279
  (Polychromatic418967fa.accept_10_5_4_9_1_420 75 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 154 279 (accept_3_5 74 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 154 279 (Polychromatic418967fa.accept_15_12_4_9_1_3204 72 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 279 (accept_3_5 71 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 154 279 (Polychromatic418967fa.accept_13_5_11_6_1_505 70 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 154 279 (accept_3_5 68 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 279 (accept_3_5 65 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 279 (Polychromatic418967fa.accept_19_7_2_13_1_4935 64 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 154 279
  (Polychromatic418967fa.accept_10_3_4_9_1_15 63 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 154 279 (accept_3_5 62 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 154 279 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 279 (accept_3_5 59 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 154 279 (accept_3_5 56 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 154 279 (accept_3_5 53 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 154 279 (Polychromatic418967fa.accept_28_24_14_27_1_17135 52
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 154 279
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 51 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 154 279 (accept_3_5 50 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 279 (accept_3_5 47 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 279 (Polychromatic418967fa.accept_16_14_10_7_1_2363 46 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 154 279 (accept_3_5 44 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 279 (accept_3_5 41 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 40 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 279
  (Polychromatic418967fa.accept_19_1_2_13_1_4934 39 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 279 (accept_3_5 38 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 279 (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 279 (accept_3_5 35 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 279 (Polychromatic418967fa.accept_13_8_11_6_1_1035 34 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 279 (accept_3_5 32 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 279 (accept_3_5 29 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 279
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 279 (accept_3_5 26 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 279 (Polychromatic418967fa.accept_20_4_14_19_1_4222 24 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 279 (accept_3_5 23 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 279 (Polychromatic418967fa.accept_21_1_7_6_1_8219 22 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 279 (accept_3_5 20 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 279 (accept_3_5 17 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 279 (Polychromatic418967fa.accept_19_16_2_13_1_13234 16
  154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 279
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 279 (accept_3_5 14 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 279 (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 279 (accept_3_5 11 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 279 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 279 (accept_3_5 8 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 279 (accept_3_5 5 154 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 279 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 154
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 279
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 279 (accept_3_5 2 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 153 279 (Eq.refl Bool.true) (allA_succ_of_gcd 126 153 279 9 14 17 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 153 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 125 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 153 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 124 153 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 153 279 3 41 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 122 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 121 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 153 279 3 40 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  119 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 118 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 153 279 9 13 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 153 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 116 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 279
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 115 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 153 279 3 38 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 113 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 279
  (Polychromatic418967fa.accept_20_12_13_19_1_8690 112 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 153 279 3 37 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 109 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 153 279 9 12 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792 107 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 153 279 3 35 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 153 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 104 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 103 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 153 279 3 34 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 101 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 279
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 100 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 153 279 9 11 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 97 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 153 279 3 32 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792 95 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 153 279 3 31 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 153 279 (Polychromatic418967fa.accept_19_16_1_13_1_4860 92 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 91 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 153 279 9 10 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 153 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 279
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 88 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 153 279 3 29 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 153 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  85 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 153 279 3 28 51 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 153 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 83 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 153 279 9 9 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 153 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676
  80 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 279 3 26 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 153 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  76 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 153 279 3 25 51 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 279 9 8 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  71 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 279 3 23 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 68 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 153 279 3 22 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 153 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  64 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 279 9 7 17 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 153 279 3 20 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 279 3 19 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 279 9 6 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 279 (Polychromatic418967fa.accept_19_14_1_13_1_7810 52 153
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 279 3 17 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 279 3 16 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 153 279 9 5 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 153 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 153
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 279 3 14 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 279 (Polychromatic418967fa.accept_15_10_3_9_1_3285 40 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 153 279 3 13 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 153 279 9 4 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 279 3 11 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 279
  (Polychromatic418967fa.accept_20_12_13_19_1_8690 32 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 153 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 279 3 10 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 279 9 3 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 279 3 8 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 279 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 279 3 7 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 279
  (Polychromatic418967fa.accept_15_5_3_9_1_283 20 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 279 9 2 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 279
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 279 3 5 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 279 3 4 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 279 9 1 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 279 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 153 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 279 3 2 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 153 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 279 3 1 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 153 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 152 279 (Eq.refl Bool.true) (allA_succ_of_accept 127 152 279 (accept_3_4 127 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 126 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 125 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 152 279 (accept_3_4 124 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 123 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 152 279 (Polychromatic418967fa.accept_17_3_16_7_1_5014 122 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 152 279 (accept_3_4 121 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 120 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 152 279 (accept_3_4 118 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 152 279 (Polychromatic418967fa.accept_10_7_2_9_1_775 117 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 116 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 152 279 (accept_3_4 115 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 114 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 113 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 152 279 (accept_3_4 112 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 152 279 (Polychromatic418967fa.accept_10_1_2_9_1_152 111 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 152 279 (Polychromatic418967fa.accept_17_8_16_7_1_8792 110 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 152 279 (accept_3_4 109 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 152 279 (Polychromatic418967fa.accept_13_4_9_6_1_2376 108 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 152 279 (accept_3_4 106 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 152 279 (Polychromatic418967fa.accept_13_1_9_6_1_146 105 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 152 279 (Polychromatic418967fa.accept_14_6_12_13_1_3180 104 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 152 279 (accept_3_4 103 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 152 279 (accept_3_4 100 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 152 279 (Polychromatic418967fa.accept_13_7_9_6_1_148 98 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 152 279 (accept_3_4 97 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 152 279 (Polychromatic418967fa.accept_18_6_8_9_1_1960 96 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 152 279 (accept_3_4 94 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 152 279 (Polychromatic418967fa.accept_13_2_9_6_1_501 93 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 152 279 (accept_3_4 91 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 152 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 90 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 152 279 (accept_3_4 88 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 152 279 (Polychromatic418967fa.accept_10_7_2_9_1_775 87 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 152 279 (Polychromatic418967fa.accept_15_11_2_9_1_1480 86 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 152 279 (accept_3_4 85 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 152 279 (Polychromatic418967fa.accept_16_4_8_7_1_3396 84 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 152 279 (accept_3_4 82 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 152 279 (Polychromatic418967fa.accept_13_2_9_6_1_501 80 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 152 279 (accept_3_4 79 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 152 279 (accept_3_4 76 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 152 279 (Polychromatic418967fa.accept_13_10_9_6_1_1026 75 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 152 279 (accept_3_4 73 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 152 279 (Polychromatic418967fa.accept_13_7_9_6_1_148 72 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 152 279 (accept_3_4 70 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 152 279 (Polychromatic418967fa.accept_13_4_9_6_1_2376 69 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 152 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 68 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 152 279 (accept_3_4 67 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 152 279 (accept_3_4 64 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 152 279 (Polychromatic418967fa.accept_16_15_8_7_1_3407 63 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 152 279 (Polychromatic418967fa.accept_13_10_9_6_1_1026 62 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 152 279 (accept_3_4 61 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 152 279 (accept_3_4 58 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 152 279 (Polychromatic418967fa.accept_13_4_9_6_1_2376 56 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 279 (accept_3_4 55 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 152 279 (accept_3_4 52 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 152 279 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 279 (accept_3_4 49 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 279 (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 152 279 (accept_3_4 46 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 152 279 (Polychromatic418967fa.accept_21_3_5_6_1_14156 45 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 152 279 (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 279 (accept_3_4 43 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 152 279 (accept_3_4 40 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 152 279 (Polychromatic418967fa.accept_15_8_2_9_1_3200 38 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 279 (accept_3_4 37 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 152 279 (accept_3_4 34 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 152 279 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 279 (accept_3_4 31 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 152 279 (accept_3_4 28 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 152 279 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 152 279 (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 279 (accept_3_4 25 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 152 279 (accept_3_4 22 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 152 279 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 152 279 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 279 (accept_3_4 19 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 152 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 279 (accept_3_4 16 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 279 (Polychromatic418967fa.accept_13_1_9_6_1_146 14 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 279 (accept_3_4 13 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 279 (Polychromatic418967fa.accept_16_12_8_7_1_4530 12 152
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 279 (accept_3_4 10 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 279 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 279 (accept_3_4 7 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 152 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 279 (accept_3_4 4 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 279 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 152 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 279 (accept_3_4 1 152 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 151 279 (Eq.refl Bool.true) (allA_succ_of_accept 128 151 279 (accept_3_5 128 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 151 279 (Polychromatic418967fa.accept_15_7_1_9_1_1500 127 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 151 279
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 126 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 151 279 (accept_3_5 125 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 124 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 151 279 (Polychromatic418967fa.accept_19_9_18_13_1_4931 123 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 151 279 (accept_3_5 122 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 121 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 151 279
  (Polychromatic418967fa.accept_21_15_4_6_1_11286 120 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 151 279 (accept_3_5 119 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 118 151 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 117 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 151 279 (accept_3_5 116 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 151 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 115 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 151 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 279 (accept_3_5 113 151 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 279
  (Polychromatic418967fa.accept_11_1_8_4_1_717 111 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 279 (accept_3_5 110 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 279 (Polychromatic418967fa.accept_19_14_18_13_1_7823 109 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 151 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 279 (accept_3_5 107 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 106 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 151 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 105 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 151 279 (accept_3_5 104 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 103 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 151 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 102 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 279 (accept_3_5 101 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 151
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 279
  (Polychromatic418967fa.accept_21_15_4_6_1_11286 99 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 151 279 (accept_3_5 98 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 151 279 (Polychromatic418967fa.accept_15_7_1_9_1_1500 97 151 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 279 (accept_3_5 95 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 94
  151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 279 (accept_3_5 92 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 279 (Polychromatic418967fa.accept_21_7_4_6_1_11287 91 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 279 (Polychromatic418967fa.accept_17_5_15_7_1_4992 90 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 279 (accept_3_5 89 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 279 (accept_3_5 86 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 84 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 279 (accept_3_5 83 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 279
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 279 (accept_3_5 80 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 279 (accept_3_5 77 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 279 (accept_3_5 74 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 279 (accept_3_5 71 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 279
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 279 (accept_3_5 68 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 67 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 279 (accept_3_5 65 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 279
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 279 (accept_3_5 62 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 279 (Polychromatic418967fa.accept_17_9_15_7_1_6212 60 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 279 (accept_3_5 59 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 279
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 279 (accept_3_5 56 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 279 (accept_3_5 53 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 279 (accept_3_5 50 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 279 (Polychromatic418967fa.accept_21_7_4_6_1_11287 49 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 279 (accept_3_5 47 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 279 (accept_3_5 44 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 279 (Polychromatic418967fa.accept_17_9_15_7_1_6212 43 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 279 (accept_3_5 41 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 279
  (Polychromatic418967fa.accept_17_5_15_7_1_4992 39 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 279 (accept_3_5 38 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 279 (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 279 (accept_3_5 35 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 279 (accept_3_5 32 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 279 (accept_3_5 29 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 279
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 279 (accept_3_5 26 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 279 (accept_3_5 23 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 279
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 279 (accept_3_5 20 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 279 (accept_3_5 17 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 279 (accept_3_5 14 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 279 (Polychromatic418967fa.accept_21_13_4_6_1_6668 13 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 279 (accept_3_5 11 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 279 (accept_3_5 8 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 279 (Polychromatic418967fa.accept_15_6_1_9_1_1476 6 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 279 (accept_3_5 5 151 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 279 (accept_3_5 2 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 151 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 150 279 (Eq.refl Bool.true) (allA_succ_of_gcd 129 150 279 3 43 50 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 150 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 128 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 150 279 (Polychromatic418967fa.accept_16_15_6_7_1_4512 127 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 150 279 3 42 50 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 125 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 150 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 124 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 150 279 3 41 50 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 150 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 122 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 279 3 40 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 279
  (Polychromatic418967fa.accept_21_14_3_6_1_8231 119 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 150 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 118 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 150 279 3 39 50 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 150 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 116 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 150 279 (Polychromatic418967fa.accept_14_3_10_13_1_339 115 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 279 3 38 50 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 150 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 112 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 150 279 3 37 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 150 279 (Polychromatic418967fa.accept_12_2_6_3_1_331
  110 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 109 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 150 279 3 36 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 150 279
  (Polychromatic418967fa.accept_12_10_6_3_1_786 106 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 150 279 3 35 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 150 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 104 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 150 279
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 103 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 150 279 3 34 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 150 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 100 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 150 279 3 33 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 150 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 98 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 279 3 32 50 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 150 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 94 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 150 279 3 31 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 150 279 (Polychromatic418967fa.accept_12_8_6_3_1_366
  92 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 150 279
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 91 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 279 3 30 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 150 279 (Polychromatic418967fa.accept_7_4_3_6_1_340
  88 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 150 279 3 29 50 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 150 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 150 279 3 28 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 279
  (Polychromatic418967fa.accept_19_7_17_13_1_9166 83 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 150 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 82 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 150 279 3 27 50 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 150 279
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 80 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 279 3 26 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 76 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 150 279 3 25 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 150 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 279 3 24 50 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 279
  (Polychromatic418967fa.accept_20_11_10_19_1_8714 71 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 150 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 150 279 3 23 50 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 150 279
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 279 3 22 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 279
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 150 279 3 21 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 150 279 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 279 3 20 50 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 279
  (Polychromatic418967fa.accept_14_3_10_13_1_339 59 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 150 279 3 19 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 150 279 (Polychromatic418967fa.accept_12_8_6_3_1_366
  56 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 279
  (Polychromatic418967fa.accept_17_4_14_7_1_4965 55 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 279 3 18 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  52 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 150 279 3 17 50 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 150 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 279 3 16 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  47 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 150 279 3 15 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 279 (Polychromatic418967fa.accept_13_4_7_6_1_2359
  43 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 279 3 14 50 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 150 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 150 279 3 13 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 279 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 279 3 12 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 279 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 150 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 279
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 150 279 3 11 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 150 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 279
  (Polychromatic418967fa.accept_14_3_10_13_1_339 31 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 279 3 10 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 279 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 150 279 3 9 50 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 150 279
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 279 3 8 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 279
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 150 279 3 7 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 150 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 279 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 150
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 279 3 6 50 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 279 3 5 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  14 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 279 3 4 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 150 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 279 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 150
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 150 279 3 3 50 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 150 279
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 279 (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 279 3 2 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 279
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 150 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 150 279 3 1 50 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 150 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 149 279 (Eq.refl Bool.true) (allA_succ_of_accept 130 149 279 (accept_3_4 130 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 129 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 128 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 149 279 (accept_3_4 127 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 149 279 (Polychromatic418967fa.accept_15_5_14_9_1_274 125 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 149 279 (accept_3_4 124 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 123 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 122 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 149 279 (accept_3_4 121 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 149 279 (Polychromatic418967fa.accept_21_14_2_6_1_11341 119 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 149 279 (accept_3_4 118 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 117 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 149 279 (accept_3_4 115 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 149 279 (accept_3_4 112 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 149 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 111
  149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 149 279 (accept_3_4 109 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 149 279 (Polychromatic418967fa.accept_16_11_5_7_1_2395 107 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 149 279 (accept_3_4 106 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 105 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 149 279 (accept_3_4 103 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 279 (accept_3_4 100 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 149 279 (accept_3_4 97 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 149 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 96 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 279 (accept_3_4 94 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 149 279 (accept_3_4 91 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 149 279 (Polychromatic418967fa.accept_25_14_24_4_1_17134 89 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 279 (accept_3_4 88 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 149 279 (accept_3_4 85 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 149 279 (Polychromatic418967fa.accept_18_12_5_9_1_6896 84 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 149 279 (Polychromatic418967fa.accept_15_8_14_9_1_4216 83 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 279 (accept_3_4 82 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 279 (accept_3_4 79 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 279 (Polychromatic418967fa.accept_19_1_16_13_1_10571 77 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 279 (accept_3_4 76 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 279 (Polychromatic418967fa.accept_16_11_5_7_1_2395 75 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 279 (accept_3_4 73 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 72 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 279 (accept_3_4 70 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 279 (accept_3_4 67 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 279 (Polychromatic418967fa.accept_15_5_14_9_1_274 65 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 279 (accept_3_4 64 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 279 (Polychromatic418967fa.accept_20_3_9_19_1_4214 63 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 279 (accept_3_4 61 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 279 (accept_3_4 58 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 279 (accept_3_4 55 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 279 (accept_3_4 52 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 279 (Polychromatic418967fa.accept_15_6_14_9_1_1471 51 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 279 (accept_3_4 49 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 279 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 279 (Polychromatic418967fa.accept_24_23_5_15_1_12055 47 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 279 (accept_3_4 46 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 279 (accept_3_4 43 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 279 (Polychromatic418967fa.accept_19_3_16_13_1_2293 41 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 279 (accept_3_4 40 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 279 (accept_3_4 37 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 279 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 279 (accept_3_4 34 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 279 (accept_3_4 31 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 279 (accept_3_4 28 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 27 149 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 279 (accept_3_4 25 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 279 (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 279 (accept_3_4 22 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 149
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 279 (accept_3_4 19 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 279 (accept_3_4 16 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 279 (accept_3_4 13 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 279 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 279 (accept_3_4 10 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 279 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 279 (accept_3_4 7 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 279 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 279 (accept_3_4 4 149 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 279 (accept_3_4 1 149 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 148 279 (Eq.refl Bool.true) (allA_succ_of_accept 131 148 279 (accept_3_5 131 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 148 279 (Polychromatic418967fa.accept_19_16_15_13_1_1335 130
  148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 148 279
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 129 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 148 279 (accept_3_5 128 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 127 148 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 148 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 126 148
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 148 279 (accept_3_5 125 148
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 148 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 124 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 148 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 123 148 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 148 279 (accept_3_5 122 148 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 121 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 148 279
  (Polychromatic418967fa.accept_11_10_5_4_1_711 120 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 148 279 (accept_3_5 119 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 148 279 (Polychromatic418967fa.accept_13_1_5_6_1_1048 118 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 148 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 148 279 (accept_3_5 116 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 148
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 148 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 114 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 148 279 (accept_3_5 113 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 148 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 112 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 148 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 111 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 148 279 (accept_3_5 110 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14
  109 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 148 279
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 108 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 148 279 (accept_3_5 107 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 148 279 (Polychromatic418967fa.accept_17_4_12_7_1_8771 106 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 148 279 (Polychromatic418967fa.accept_13_1_5_6_1_1048 105 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 148 279 (accept_3_5 104 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14
  103 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 102 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 148 279 (accept_3_5 101 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 148 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 148 279 (accept_3_5 98 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 148 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 148 279 (accept_3_5 95 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 148 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 94 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 148 279 (accept_3_5 92 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 90 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 148 279 (accept_3_5 89 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 148 279 (Polychromatic418967fa.accept_13_10_5_6_1_1671 88 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 148 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 87 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 148 279 (accept_3_5 86 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 148 279
  (Polychromatic418967fa.accept_10_4_8_9_1_784 84 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 148 279 (accept_3_5 83 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 148 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 148 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 81 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 279 (accept_3_5 80 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 78 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 148 279 (accept_3_5 77 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 148 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 76 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 148 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 279 (accept_3_5 74 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 148 279 (accept_3_5 71 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 148 279 (Polychromatic418967fa.accept_17_2_12_7_1_7429 70 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 148 279 (Polychromatic418967fa.accept_13_4_5_6_1_3201 69 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 279 (accept_3_5 68 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 279 (accept_3_5 65 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 279 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 279 (accept_3_5 62 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 279
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 60 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 279 (accept_3_5 59 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 279 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 279 (accept_3_5 56 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 279 (accept_3_5 53 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 279 (accept_3_5 50 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 279
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 48 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 279 (accept_3_5 47 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 279 (Polychromatic418967fa.accept_16_14_4_7_1_2380 46 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 279 (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 279 (accept_3_5 44 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 279 (accept_3_5 41 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 279 (Polychromatic418967fa.accept_17_5_12_7_1_2651 39 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 279 (accept_3_5 38 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 279
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 279 (accept_3_5 35 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 279 (accept_3_5 32 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 279 (accept_3_5 29 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 279 (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 279 (accept_3_5 26 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 279
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 279 (accept_3_5 23 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 279 (Polychromatic418967fa.accept_15_7_13_9_1_1466 22 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 279 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 279 (accept_3_5 20 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 279 (accept_3_5 17 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 279 (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 279 (accept_3_5 14 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 279 (accept_3_5 11 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 279 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 279 (accept_3_5 8 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 279
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 279 (accept_3_5 5 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 279 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 148 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 279 (accept_3_5 2 148 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 147 279 (Eq.refl Bool.true) (allA_succ_of_gcd 132 147 279 3 44 49 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 147 279
  (Polychromatic418967fa.accept_23_16_9_3_1_10742 131 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 147 279 (Polychromatic418967fa.accept_15_10_12_9_1_776 130 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 129 147 279 3 43 49 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 147 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 128 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 147 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 127 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 147 279 3 42 49 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 147 279
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 125 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 124 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 147 279 3 41 49 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 147 279
  (Polychromatic418967fa.accept_10_2_7_9_1_783 122 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 147 279 (Polychromatic418967fa.accept_16_9_3_7_1_6883 121 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 147 279 3 40 49 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 147 279
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 119 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 147 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 118 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 147 279 3 39 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491
  116 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 279
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 115 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 147 279 3 38 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 147 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 113 147 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 147 279
  (Polychromatic418967fa.accept_10_2_7_9_1_783 112 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 147 279 3 37 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 147 279 (Polychromatic418967fa.accept_15_5_12_9_1_2253 110 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 279
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 109 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 147 279 3 36 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 147 279 (Polychromatic418967fa.accept_16_11_3_7_1_2375 107 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 147 279
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 106 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 147 279 3 35 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 147 279 (Polychromatic418967fa.accept_14_6_7_13_1_3158 104 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 279
  (Polychromatic418967fa.accept_17_1_11_7_1_4962 103 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 147 279 3 34 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 147 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 101 147 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 100 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 147 279 3 33 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 147 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 98 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 279 (Polychromatic418967fa.accept_18_7_3_9_1_1020
  97 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 147 279 3 32 49 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 147 279
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 95 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 147 279 (Polychromatic418967fa.accept_15_4_12_9_1_773 94 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 147 279 3 31 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 92
  147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 279
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 91 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 147 279 3 30 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 147 279 (Polychromatic418967fa.accept_13_11_4_6_1_1006 89 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 88 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 147 279 3 29 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 279 (Polychromatic418967fa.accept_17_1_11_7_1_4962 86 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 279
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 85 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 147 279 3 28 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 147 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371 83 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 279
  (Polychromatic418967fa.accept_10_2_7_9_1_783 82 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 147 279 3 27 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 147 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356 80 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 279
  (Polychromatic418967fa.accept_15_4_12_9_1_773 79 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 147 279 3 26 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 147 279 (Polychromatic418967fa.accept_19_1_14_13_1_6294 77 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 76 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 147 279 3 25 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 147 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 74 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 279
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 73 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 147 279 3 24 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 147 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 71 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 279
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 70 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 147 279 3 23 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 279 (Polychromatic418967fa.accept_13_2_4_6_1_2356
  67 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 147 279 3 22 49 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 147 279
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 65 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 279 (Polychromatic418967fa.accept_14_8_7_13_1_4113 64 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 147 279 3 21 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 147 279 (Polychromatic418967fa.accept_10_2_7_9_1_783
  62 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 279
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 61 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 147 279 3 20 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 147 279 (Polychromatic418967fa.accept_13_7_4_6_1_3221 59 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 58 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 147 279 3 19 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 147 279 (Polychromatic418967fa.accept_17_5_11_7_1_6146 56 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 279
  (Polychromatic418967fa.accept_15_10_12_9_1_776 55 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 147 279 3 18 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 147 279 (Polychromatic418967fa.accept_19_15_14_13_1_2343 53 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 147 279 3 17 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 147 279 (Polychromatic418967fa.accept_13_11_4_6_1_1006 50 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 279
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 279 3 16 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 279 (Polychromatic418967fa.accept_16_15_3_7_1_3389 47 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 279
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 46 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 279 3 15 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 279 (Polychromatic418967fa.accept_14_1_7_13_1_333
  43 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 279 3 14 49 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 279
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 279 (Polychromatic418967fa.accept_15_10_12_9_1_776 40 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 279 3 13 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 279 (Polychromatic418967fa.accept_10_8_7_9_1_425
  38 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 279
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 147 279 3 12 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 147 279 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 279
  (Polychromatic418967fa.accept_14_6_7_13_1_3158 34 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 279 3 11 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 147 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371
  31 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 279 3 10 49 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 279
  (Polychromatic418967fa.accept_14_1_7_13_1_333 29 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 279 3 9 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 279 (Polychromatic418967fa.accept_16_10_3_7_1_8094
  26 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 279
  (Polychromatic418967fa.accept_15_10_12_9_1_776 25 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 147 279 3 8 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 147 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 279 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 147
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 279 3 7 49 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 279 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 279 3 6 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 279
  (Polychromatic418967fa.accept_20_17_7_19_1_13006 17 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 147 279 (Polychromatic418967fa.accept_19_16_14_13_1_2313 16 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 279 3 5 49 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 279
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 279 (Polychromatic418967fa.accept_17_13_11_7_1_4961 13 147 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 279 3 4 49 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 279
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 279 3 3 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 279 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 147 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 279
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 147 279 3 2 49 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 279 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 279 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 279 3 1 49 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 279
  (Polychromatic418967fa.accept_10_2_7_9_1_783 2 147 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 279 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 147 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 146 279 (Eq.refl Bool.true) (allA_succ_of_accept 133 146 279 (accept_3_4 133 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 146 279 (Polychromatic418967fa.accept_18_6_2_9_1_3056 132 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 131 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 146 279 (accept_3_4 130 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 129 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 146 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 128 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 146 279 (accept_3_4 127 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 126 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 125 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 146 279 (accept_3_4 124 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 146 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 123 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 146 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 122 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 146 279 (accept_3_4 121 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 146 279 (Polychromatic418967fa.accept_17_1_10_7_1_12461 120
  146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 146 279 (accept_3_4 118 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 146 279 (Polychromatic418967fa.accept_17_14_10_7_1_2670 116 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 146 279 (accept_3_4 115 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 114 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 146 279 (accept_3_4 112 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 146 279 (Polychromatic418967fa.accept_15_6_11_9_1_3215 111 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 146 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 110 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 146 279 (accept_3_4 109 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 146 279
  (Polychromatic418967fa.accept_16_12_2_7_1_6853 108 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 146 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 107 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 146 279 (accept_3_4 106 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 146 279
  (Polychromatic418967fa.accept_24_8_2_15_1_6933 104 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 146 279 (accept_3_4 103 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 102 146 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 146 279 (accept_3_4 100 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 146 279
  (Polychromatic418967fa.accept_17_14_10_7_1_2670 99 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 146 279 (Polychromatic418967fa.accept_21_14_20_6_1_9817 98 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 146 279 (accept_3_4 97 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 146 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 96 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 146 279 (accept_3_4 94 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 146 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 92 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 146 279 (accept_3_4 91 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 146 279 (accept_3_4 88 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 146 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 87 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 146 279 (Polychromatic418967fa.accept_17_1_10_7_1_12461 86 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 146 279 (accept_3_4 85 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 146 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 84 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 146 279 (accept_3_4 82 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 146 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 80 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 146 279 (accept_3_4 79 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 146 279 (accept_3_4 76 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 146 279 (Polychromatic418967fa.accept_10_5_6_9_1_2235 75 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 146 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 74 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 146 279 (accept_3_4 73 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 146 279 (Polychromatic418967fa.accept_21_9_20_6_1_9815 72 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 146 279 (accept_3_4 70 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 146 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 68 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 146 279 (accept_3_4 67 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 146 279 (accept_3_4 64 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 146 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 146 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 62 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 146 279 (accept_3_4 61 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 146 279 (Polychromatic418967fa.accept_16_12_2_7_1_6853 60 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 146 279 (accept_3_4 58 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 146 279 (Polychromatic418967fa.accept_21_14_20_6_1_9817 56 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 146 279 (accept_3_4 55 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 146 279 (accept_3_4 52 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 146 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 146 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 50 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 146 279 (accept_3_4 49 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 146 279 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 146 279 (accept_3_4 46 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 146 279 (Polychromatic418967fa.accept_13_5_3_6_1_3278 44 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 146 279 (accept_3_4 43 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 146 279 (accept_3_4 40 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 146 279 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 146 279 (Polychromatic418967fa.accept_29_9_1_18_1_17133 38 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 146 279 (accept_3_4 37 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 146 279 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 146 279 (accept_3_4 34 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 146 279 (Polychromatic418967fa.accept_15_2_11_9_1_263 32 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 279 (accept_3_4 31 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 279 (accept_3_4 28 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 279 (accept_3_4 25 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 279 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 279 (accept_3_4 22 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 279 (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 279 (accept_3_4 19 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 279 (accept_3_4 16 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 279 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 279 (accept_3_4 13 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 279 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 146
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 279 (accept_3_4 10 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 279 (Polychromatic418967fa.accept_24_8_2_15_1_6933 8 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 279 (accept_3_4 7 146 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 279 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 146 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 279 (accept_3_4 4 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 279 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 146 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 279 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 146 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 279 (accept_3_4 1 146 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 145 279 (Eq.refl Bool.true) (allA_succ_of_accept 134 145 279 (accept_3_5 134 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 145 279 (Polychromatic418967fa.accept_20_13_5_19_1_10110 133
  145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 145 279
  (Polychromatic418967fa.accept_14_6_5_13_1_367 132 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 145 279 (accept_3_5 131 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 130 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 129 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 145 279 (accept_3_5 128 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 127 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 126 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 145 279 (accept_3_5 125 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 124 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 123 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 145 279 (accept_3_5 122 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 121 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 145 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 120 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 145 279 (accept_3_5 119 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 117 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 145 279 (accept_3_5 116 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 145 279 (Polychromatic418967fa.accept_19_1_12_13_1_6279 115
  145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 145 279 (accept_3_5 113 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 112 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 111 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 145 279 (accept_3_5 110 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 145 279
  (Polychromatic418967fa.accept_11_9_2_4_1_707 108 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 145 279 (accept_3_5 107 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 145 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 105 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 145 279 (accept_3_5 104 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 145 279 (Polychromatic418967fa.accept_13_12_2_6_1_2396 103
  145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 145 279 (accept_3_5 101 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 279 (accept_3_5 98 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 97 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 279
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 145 279 (accept_3_5 95 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 93 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 279 (accept_3_5 92 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 91 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 145 279 (accept_3_5 89 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 145 279 (Polychromatic418967fa.accept_13_9_2_6_1_514 87 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 279 (accept_3_5 86 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 279
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 145 279 (accept_3_5 83 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 279 (accept_3_5 80 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 145 279 (Polychromatic418967fa.accept_13_1_2_6_1_515 79 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 145 279 (accept_3_5 77 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 145 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 75 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 279 (accept_3_5 74 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 279 (Polychromatic418967fa.accept_13_8_2_6_1_2385 73 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 279
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 279 (accept_3_5 71 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 279 (accept_3_5 68 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 279 (accept_3_5 65 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 279 (Polychromatic418967fa.accept_15_3_10_9_1_769 63 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 279 (accept_3_5 62 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 279 (accept_3_5 59 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 279 (accept_3_5 56 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 279 (Polychromatic418967fa.accept_20_15_5_19_1_5686 55 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 279 (accept_3_5 53 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 279 (accept_3_5 50 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 279 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 279
  (Polychromatic418967fa.accept_13_9_2_6_1_514 48 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 279 (accept_3_5 47 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 279 (accept_3_5 44 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 279 (accept_3_5 41 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 279 (accept_3_5 38 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 279 (Polychromatic418967fa.accept_19_18_12_13_1_2311 37 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 279
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 279 (accept_3_5 35 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 279 (accept_3_5 32 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 279 (accept_3_5 29 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 279 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 279 (accept_3_5 26 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 279
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 279 (accept_3_5 23 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 279 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 279 (accept_3_5 20 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 279 (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 145
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 279 (accept_3_5 17 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 279 (accept_3_5 14 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 279 (Polychromatic418967fa.accept_20_13_5_19_1_10110 13 145 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 279
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 279 (accept_3_5 11 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 279 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 279 (accept_3_5 8 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 279 (Polychromatic418967fa.accept_22_7_13_15_1_9473 7 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 279 (accept_3_5 5 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 279 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 279 (accept_3_5 2 145 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 144 279 (Eq.refl Bool.true) (allA_succ_of_gcd 135 144 279 9 15 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 144 279
  (Polychromatic418967fa.accept_20_14_4_19_1_4288 134 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 144 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 133 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 144 279 3 44 48 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 144 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 131 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 144 279 (Polychromatic418967fa.accept_19_16_11_13_1_4944 130 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 129 144 279 3 43 48 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 128 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 144 279 (Polychromatic418967fa.accept_29_11_28_18_1_17132 127 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 279 9 14 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 279
  (Polychromatic418967fa.accept_10_5_4_9_1_420 125 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 124 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 144 279 3 41 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329
  122 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 121 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 144 279 3 40 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 144 279 (Polychromatic418967fa.accept_13_2_1_6_1_2365 119 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 144 279
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 118 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 144 279 9 13 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 144 279 (Polychromatic418967fa.accept_17_14_8_7_1_6183 116 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 144 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 115 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 144 279 3 38 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 144 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 113 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 144 279
  (Polychromatic418967fa.accept_13_8_1_6_1_997 112 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 144 279 3 37 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 110 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 144 279
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 109 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 144 279 9 12 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 107 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 144 279
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 106 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 144 279 3 35 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 144 279 (Polychromatic418967fa.accept_21_20_18_6_1_5094 104 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 144 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 103 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 144 279 3 34 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 100 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 144 279 9 11 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 144 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 144 279
  (Polychromatic418967fa.accept_19_2_11_13_1_9180 97 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 144 279 3 32 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 144 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 95 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 144 279
  (Polychromatic418967fa.accept_7_3_4_6_1_329 94 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 144 279 3 31 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 144 279 (Polychromatic418967fa.accept_19_16_11_13_1_4944 92 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 144 279
  (Polychromatic418967fa.accept_21_7_18_6_1_9797 91 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 279 9 10 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 144 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  88 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 144 279 3 29 48 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 144 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 85 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 279 3 28 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 83
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 82 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 144 279 9 9 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 144 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 144 279 3 26 48 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 144 279
  (Polychromatic418967fa.accept_21_14_18_6_1_12747 77 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 144 279 (Polychromatic418967fa.accept_21_13_18_6_1_6676 76 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 144 279 3 25 48 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 144 279
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 74 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 279 9 8 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 279
  (Polychromatic418967fa.accept_22_5_12_15_1_17131 71 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 144 279 (Polychromatic418967fa.accept_13_5_1_6_1_2367 70 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 144 279 3 23 48 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 144 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 144 279 (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 279 3 22 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 279
  (Polychromatic418967fa.accept_19_7_11_13_1_11853 64 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 144 279 9 7 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 144 279 (Polychromatic418967fa.accept_19_5_11_13_1_11852 62 144 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 279 3 20 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166
  58 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 144 279 3 19 48 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 144 279
  (Polychromatic418967fa.accept_21_14_18_6_1_12747 56 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 144 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 55 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 279 9 6 16 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 279
  (Polychromatic418967fa.accept_10_3_4_9_1_15 53 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 144 279 3 17 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 144 279 (Polychromatic418967fa.accept_17_16_8_7_1_4983
  50 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 279
  (Polychromatic418967fa.accept_20_9_4_19_1_10052 49 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 144 279 3 16 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 144 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 279
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 46 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 144 279 9 5 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 144 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 279 3 14 48 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 279
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 144 279 3 13 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 38
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 279 9 4 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 279 (Polychromatic418967fa.accept_13_8_1_6_1_997 34 144
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 144 279 3 11 48 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 144 279
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 32 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 279 3 10 48 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 279
  (Polychromatic418967fa.accept_13_3_1_6_1_509 29 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 144 279 9 3 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 279
  (Polychromatic418967fa.accept_10_5_4_9_1_420 25 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 279 3 8 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 279 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 144
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 279 3 7 48 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 279
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 279 9 2 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 144 279 3 5 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 144 279 (Polychromatic418967fa.accept_17_14_8_7_1_6183 14 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 144 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 279 3 4 48 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 279
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 11 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 144 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 144 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 279 9 1 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 279 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8
  144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 279
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 279 3 2 48 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 279 (Polychromatic418967fa.accept_17_4_8_7_1_7469 4 144 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 279 3 1 48 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 279
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 144 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 279 (Polychromatic418967fa.accept_17_1_8_7_1_4982 1 144 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 143 279 (Eq.refl Bool.true) (allA_succ_of_accept 136 143 279 (accept_3_4 136 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 135 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 134 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 143 279 (accept_3_4 133 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  132 143 279 (Polychromatic418967fa.accept_26_2_13_19_1_17130 132 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 131 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 143 279 (accept_3_4 130 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 143 279
  (Polychromatic418967fa.accept_12_9_11_3_1_772 129 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 143 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 128 143 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 279 (accept_3_4 127 143 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 143 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 126 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 279
  (Polychromatic418967fa.accept_23_10_5_3_1_7289 125 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 143 279 (accept_3_4 124 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 123 143 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 143 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 122 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 279 (accept_3_4 121 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 279
  (Polychromatic418967fa.accept_16_8_15_7_1_5658 120 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 143 279 (Polychromatic418967fa.accept_15_14_8_9_1_1452 119 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 143 279 (accept_3_4 118 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 117 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 116 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 143 279 (accept_3_4 115 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 143 279 (Polychromatic418967fa.accept_23_21_5_3_1_10757 113 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 279 (accept_3_4 112 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 279 (Polychromatic418967fa.accept_19_16_10_13_1_4922 111
  143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 143 279 (accept_3_4 109 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 143 279 (Polychromatic418967fa.accept_14_10_3_13_1_1530 108 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 143 279 (accept_3_4 106 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 105 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 143 279 (accept_3_4 103 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 143 279 (Polychromatic418967fa.accept_19_6_10_13_1_4839 101 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 279 (accept_3_4 100 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 99 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 143 279 (accept_3_4 97 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 143 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 96 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 95 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 279 (accept_3_4 94 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 143 279 (accept_3_4 91 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 143 279 (Polychromatic418967fa.accept_20_10_3_19_1_2931 90 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 143 279 (Polychromatic418967fa.accept_15_14_8_9_1_1452 89 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 143 279 (accept_3_4 88 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 143 279 (Polychromatic418967fa.accept_18_15_17_9_1_4200 87 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 143 279 (accept_3_4 85 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 143 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 143 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 83 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 279 (accept_3_4 82 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 279 (accept_3_4 79 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 78 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 143 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 77 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 279 (accept_3_4 76 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 279 (Polychromatic418967fa.accept_16_11_15_7_1_5654 75 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 279 (accept_3_4 73 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 279 (Polychromatic418967fa.accept_22_5_11_15_1_7870 71 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 279 (accept_3_4 70 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 279 (accept_3_4 67 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 66 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 279 (accept_3_4 64 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 63 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 279 (accept_3_4 61 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 279 (Polychromatic418967fa.accept_15_14_8_9_1_1452 59 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 279 (accept_3_4 58 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 279 (accept_3_4 55 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 279 (accept_3_4 52 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 279 (accept_3_4 49 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 48 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 47 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 279 (accept_3_4 46 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 279 (accept_3_4 43 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 279 (Polychromatic418967fa.accept_19_4_10_13_1_7814 42 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 279 (Polychromatic418967fa.accept_19_3_10_13_1_3482 41 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 279 (accept_3_4 40 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 279 (accept_3_4 37 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 279 (Polychromatic418967fa.accept_16_3_15_7_1_3417 35 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 279 (accept_3_4 34 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 279 (accept_3_4 31 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 279 (Polychromatic418967fa.accept_15_14_8_9_1_1452 29 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 279 (accept_3_4 28 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 279 (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 279 (accept_3_4 25 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 279 (accept_3_4 22 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 279 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 279 (accept_3_4 19 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 279 (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 279 (accept_3_4 16 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 279 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 143
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 279 (accept_3_4 13 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 279 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 279 (accept_3_4 10 143 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 279 (accept_3_4 7 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 279 (Polychromatic418967fa.accept_19_5_10_13_1_4883 5 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 279 (accept_3_4 4 143 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 279 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 143 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 279
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 279 (accept_3_4 1 143 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 142 279 (Eq.refl Bool.true) (allA_succ_of_accept 137 142 279 (accept_3_5 137 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 136 142
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 142 279
  (Polychromatic418967fa.accept_13_5_12_6_1_508 135 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 142 279 (accept_3_5 134 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 133 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 142 279 (Polychromatic418967fa.accept_13_2_12_6_1_2394 132 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 142 279 (accept_3_5 131 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 130 142
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 129 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 142 279 (accept_3_5 128 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 127 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 142 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 126 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 142 279 (accept_3_5 125 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 142 279 (Polychromatic418967fa.accept_13_7_12_6_1_1039 124
  142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 142 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 123 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 142 279 (accept_3_5 122 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 121 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 142 279 (accept_3_5 119 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 142 279 (Polychromatic418967fa.accept_15_13_7_9_1_3210 118
  142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 142 279 (accept_3_5 116 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 115 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 142 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 114 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 142 279 (accept_3_5 113 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 142 279 (Polychromatic418967fa.accept_19_17_9_13_1_6325 112
  142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 142 279
  (Polychromatic418967fa.accept_10_1_2_9_1_152 111 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 142 279 (accept_3_5 110 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 142 279 (accept_3_5 107 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 142
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 142 279 (accept_3_5 104 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 142 279 (accept_3_5 101 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 142 279 (Polychromatic418967fa.accept_16_4_14_7_1_5641 100
  142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 142 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 142 279 (accept_3_5 98 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 142 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 96 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 142 279 (accept_3_5 95 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 142 279 (accept_3_5 92 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 142 279 (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 142 279 (accept_3_5 89 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 142 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 142 279 (accept_3_5 86 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 142 279 (Polychromatic418967fa.accept_16_4_14_7_1_5641 84 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 142 279 (accept_3_5 83 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 142 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 82 142
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 142 279 (accept_3_5 80 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 142 279 (accept_3_5 77 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 142 279 (Polychromatic418967fa.accept_15_1_7_9_1_20 76 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 142 279
  (Polychromatic418967fa.accept_13_10_12_6_1_991 75 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 142 279 (accept_3_5 74 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 142 279 (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 142 279 (accept_3_5 71 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 142 279 (Polychromatic418967fa.accept_13_5_12_6_1_508 70 142
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 142 279 (accept_3_5 68 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 142 279 (accept_3_5 65 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 142 279
  (Polychromatic418967fa.accept_16_15_14_7_1_10555 63 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 142 279 (accept_3_5 62 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 142 279 (accept_3_5 59 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 142 279
  (Polychromatic418967fa.accept_15_13_7_9_1_3210 58 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 279 (accept_3_5 56 142 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 279 (accept_3_5 53 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 279 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 279 (accept_3_5 50 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 279
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 48 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 279 (accept_3_5 47 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 279 (accept_3_5 44 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 279 (accept_3_5 41 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 279 (Polychromatic418967fa.accept_27_13_7_9_1_9612 40 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 279 (accept_3_5 38 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 279
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 279 (accept_3_5 35 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 279 (Polychromatic418967fa.accept_19_15_9_13_1_4838 34 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 279 (accept_3_5 32 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 279 (accept_3_5 29 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 279 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 279 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 279 (accept_3_5 26 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 279 (accept_3_5 23 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 279 (accept_3_5 20 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 279 (accept_3_5 17 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 279 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 279 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 279 (accept_3_5 14 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 279
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 142 279 (accept_3_5 11 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 142 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 279 (accept_3_5 8 142 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 279 (accept_3_5 5 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 279 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 142 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 279 (accept_3_5 2 142 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 139 141 279 (Eq.refl Bool.true) (allA_succ_of_gcd 138 141 279 3 46 47 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 141 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 137 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 141 279 (Polychromatic418967fa.accept_15_1_6_9_1_254 136 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 135 141 279 3 45 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27
  134 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 141 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 133 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 141 279 3 44 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 141 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 131 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 130 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 129 141 279 3 43 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 128 141 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 128 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 127 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 141 279 3 42 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 141 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 125 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 141 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 124 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 141 279 3 41 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 279 (Polychromatic418967fa.accept_7_2_1_6_1_173
  121 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 141 279 3 40 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 141 279
  (Polychromatic418967fa.accept_12_11_9_3_1_792 119 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 118 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 141 279 3 39 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 141 279
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 116 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 141 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 115 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 141 279 3 38 47 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 141 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 113 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248 112 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 141 279 3 37 47 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 141 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 109 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 141 279 3 36 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 141 279 (Polychromatic418967fa.accept_7_2_1_6_1_173
  107 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 141 279 3 35 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 141 279 (Polychromatic418967fa.accept_15_14_6_9_1_2274 104 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 141 279 3 34 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 141 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 101 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 141 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 100 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 141 279 3 33 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 279 (Polychromatic418967fa.accept_12_1_9_3_1_370
  97 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 141 279 3 32 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 141 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 95 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 141 279 3 31 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 141 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  92 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 279
  (Polychromatic418967fa.accept_12_7_9_3_1_767 91 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 141 279 3 30 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 141 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 279 (Polychromatic418967fa.accept_10_8_1_9_1_413
  88 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 141 279 3 29 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 141 279 3 28 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 141 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  83 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 141 279 3 27 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 141 279 (Polychromatic418967fa.accept_17_12_5_7_1_6179 80 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 141 279 3 26 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 141 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 279 (Polychromatic418967fa.accept_15_1_6_9_1_254
  76 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 141 279 3 25 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 141 279 3 24 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 141 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  71 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 141 279 3 23 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 279 (Polychromatic418967fa.accept_12_7_9_3_1_767
  67 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 141 279 3 22 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 141 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 279 (Polychromatic418967fa.accept_15_4_6_9_1_2269 64 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 141 279 3 21 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 279 3 20 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 279 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 141 279 3 19 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 141 279 (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 141 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 279
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 141 279 3 18 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 141 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 279 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  52 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 141 279 3 17 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 279 3 16 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 141 279 3 15 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 141 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 279 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 141 279 3 14 47 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 279
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 279 3 13 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 279 3 12 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 141 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 279 3 11 47 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 279
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 279 3 10 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 279
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 141 279 3 9 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 279 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 141
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 279 3 8 47 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 279
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 279 3 7 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 279 (Polychromatic418967fa.accept_16_4_13_7_1_4522
  20 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 141 279 3 6 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 141 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 279 3 5 47 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 279 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 279 3 4 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 279 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 279 3 3 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 279 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 279 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 141 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 279 3 2 47 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 279
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 279 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 141 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 279 3 1 47 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 279
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141
  279)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 279 (allA_succ_of_accept 139 140 279 (accept_3_4 139 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 138 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 138 140 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 140 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 137 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 140 279 (accept_3_4 136 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 140 279
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 135 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 140 279 (Polychromatic418967fa.accept_13_4_10_6_1_989 134 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 140 279 (accept_3_4 133 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 140 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 132
  140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 131 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 140 279 (accept_3_4 130 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 140 279 (Polychromatic418967fa.accept_13_12_10_6_1_3212 129 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 128 140 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 128 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 140 279 (accept_3_4 127 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82
  126 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 125 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 140 279 (accept_3_4 124 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 123 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 122 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 140 279 (accept_3_4 121 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 140 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 120
  140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 119 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 140 279 (accept_3_4 118 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 140 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 117 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 140 279 (Polychromatic418967fa.accept_13_12_10_6_1_3212 116 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 140 279 (accept_3_4 115 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 114 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 113 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 140 279 (accept_3_4 112 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 111 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 140 279 (Polychromatic418967fa.accept_17_8_4_7_1_7442 110 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 140 279 (accept_3_4 109 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 140 279 (Polychromatic418967fa.accept_13_4_10_6_1_989 108 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 140 279 (accept_3_4 106 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 140 279 (Polychromatic418967fa.accept_17_3_4_7_1_1658 105 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 140 279 (Polychromatic418967fa.accept_15_14_5_9_1_2284 104 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 140 279 (accept_3_4 103 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 140 279 (accept_3_4 100 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 140 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 98 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 140 279 (accept_3_4 97 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 140 279 (Polychromatic418967fa.accept_13_5_10_6_1_2361 96 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 140 279 (accept_3_4 94 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 140 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 93 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 140 279 (Polychromatic418967fa.accept_21_8_14_6_1_9800 92 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 140 279 (accept_3_4 91 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 140 279 (accept_3_4 88 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 140 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 87 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 140 279 (Polychromatic418967fa.accept_15_11_5_9_1_3205 86 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 140 279 (accept_3_4 85 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 140 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 84 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 140 279 (accept_3_4 82 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 140 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 81 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 140 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 80 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 140 279 (accept_3_4 79 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 78 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 140 279 (accept_3_4 76 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 140 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 74 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 140 279 (accept_3_4 73 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 140 279 (Polychromatic418967fa.accept_15_12_5_9_1_3234 72 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 140 279 (accept_3_4 70 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 140 279 (Polychromatic418967fa.accept_13_4_10_6_1_989 69 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 140 279 (Polychromatic418967fa.accept_13_3_10_6_1_2382 68 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 140 279 (accept_3_4 67 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 140 279 (accept_3_4 64 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 140 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 63 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 140 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 62 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 140 279 (accept_3_4 61 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 140 279 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 140 279 (accept_3_4 58 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 140 279 (Polychromatic418967fa.accept_13_5_10_6_1_2361 57 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 56 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 140 279 (accept_3_4 55 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 140 279 (accept_3_4 52 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 140 279 (Polychromatic418967fa.accept_16_2_12_7_1_3410 50 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 140 279 (accept_3_4 49 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 140 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 140 279 (accept_3_4 46 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 140 279 (Polychromatic418967fa.accept_13_5_10_6_1_2361 44 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 140 279 (accept_3_4 43 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 140 279 (accept_3_4 40 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 140 279 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 140 279 (Polychromatic418967fa.accept_13_12_10_6_1_3212 38 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 279 (accept_3_4 37 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 279 (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 140 279 (accept_3_4 34 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 279 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 279 (Polychromatic418967fa.accept_21_11_14_6_1_8311 32 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 279 (accept_3_4 31 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 140 279 (accept_3_4 28 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 279 (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 279 (accept_3_4 25 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 279 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 279 (accept_3_4 22 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 279 (Polychromatic418967fa.accept_16_5_12_7_1_3411 21 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 279 (Polychromatic418967fa.accept_16_4_12_7_1_4475 20 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 279 (accept_3_4 19 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 279 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 279 (accept_3_4 16 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 279 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 279 (accept_3_4 13 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 279 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 140
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 279 (accept_3_4 10 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 279 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 279 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 279 (accept_3_4 7 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 279
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 279 (accept_3_4 4 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 279 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 140 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 279 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 279 (accept_3_4 1 140 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 140
  279))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_279_segment_001))))))))))))))))))))))))))))))))))))))))


