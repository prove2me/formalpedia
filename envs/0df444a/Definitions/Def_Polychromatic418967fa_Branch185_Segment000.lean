-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch185_Segment000
-- name    : Polychromatic418967fa_Branch185_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:28:03.1413+00:00
-- url     : https://prove2.me/theorems/b8e0b3d6-45ae-4b94-9ba5-9e01b5f8f1d8
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

def Polychromatic418967fa.branch_185_segment_000 : allB 140 185 :=
  allB_succ' 47 139 185 (Eq.refl Bool.true) (allA_of_3_0 47 139 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  48 138 185 (Eq.refl Bool.true) (allA_succ_of_accept 47 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 185 (accept_3_2 46 138 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 185 (Polychromatic418967fa.accept_18_9_12_5_1_864
  45 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 185 (accept_3_2 43 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 185 (Polychromatic418967fa.accept_17_7_2_15_1_1255 41 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 185 (accept_3_2 40 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 185 (accept_3_2 37 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 185 (accept_3_2 34 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 185 (accept_3_2 31 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 138 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 185 (accept_3_2 28 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 185 (accept_3_2 25 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 185 (accept_3_2 22 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 185 (accept_3_2 19 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 185 (accept_3_2 16 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 185
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 185 (accept_3_2 13 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 185 (accept_3_2 10 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 185 (accept_3_2 7 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 185 (accept_3_2 4 138 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 185 (accept_3_2 1 138 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  185)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 137 185 (Eq.refl Bool.true) (allA_succ_of_accept 48
  137 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 185 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 185 (accept_3_2 46 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 185 (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 137
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 185 (accept_3_2 43 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 185 (accept_3_2 40 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 185
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 185 (accept_3_2 37 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 185 (accept_3_2 34 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 185
  (Polychromatic418967fa.accept_10_2_7_5_1_605 32 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 185 (accept_3_2 31 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 185 (accept_3_2 28 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 185 (accept_3_2 25 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 185 (accept_3_2 22 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 137 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 185 (accept_3_2 19 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 185 (accept_3_2 16 137 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 185
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 185 (accept_3_2 13 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 185 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 185 (accept_3_2 10 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 185 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 137 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 185 (accept_3_2 7 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 185 (Polychromatic418967fa.accept_21_5_11_17_1_10652 5 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 185 (accept_3_2 4 137 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 137 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 185
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 185 (accept_3_2 1 137 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  185))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 136 185 (Eq.refl Bool.true) (allA_of_3_0 50 136
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 135 185 (Eq.refl Bool.true) (allA_succ_of_gcd 50 135 185 5
  10 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 135
  185 (accept_3_2 49 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 135 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 185 (accept_3_2 46 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 135 185 5 9 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 135 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 185 (accept_3_2 43 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 135 185 5 8 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 135 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 185 (accept_3_2 37 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 185 (Polychromatic418967fa.accept_7_1_2_3_1_257
  36 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 185 5 7 27 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 185
  (accept_3_2 34 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 185 (accept_3_2 31 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 185 5 6 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 185 (accept_3_2 28 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 135 185 5 5 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 135 185 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 185 (Polychromatic418967fa.accept_19_4_2_14_1_10651 23 135
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 185 (accept_3_2 22 135
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 185
  (Polychromatic418967fa.accept_12_9_3_5_1_423 21 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 135 185 5 4 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 135 185 (accept_3_2 19 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 185 (accept_3_2 16 135 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 185 5 3 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 185 (accept_3_2 13
  135 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 185 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 185 5 2 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9
  135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 185 (accept_3_2 7 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 135 185 5 1 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 135 185 (accept_3_2 4 135 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 135 185 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3 135 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 185 (accept_3_2 1 135 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 185)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 134 185 (Eq.refl Bool.true) (allA_succ_of_accept 51 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50
  51 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 185
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 50 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 185 (accept_3_2 49 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 185 (accept_3_2 46 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 185 (accept_3_2 43 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 185 (accept_3_2 40 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 185 (accept_3_2 37 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 185 (accept_3_2 34 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 185 (accept_3_2 31 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 185 (accept_3_2 28 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 185 (accept_3_2 25 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 185 (accept_3_2 22 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 185 (accept_3_2 19 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 185 (accept_3_2 16 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 185
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 185 (accept_3_2 13 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 185 (accept_3_2 10 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 185 (accept_3_2 7 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 185 (accept_3_2 4 134 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 185 (accept_3_2 1 134 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  185)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 133 185 (Eq.refl Bool.true) (allA_of_3_0 53 133
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 132 185 (Eq.refl Bool.true) (allA_succ_of_accept 53 132
  185 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 132 185 (accept_3_2 52 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 132 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 185 (Polychromatic418967fa.accept_13_11_2_3_1_883 50 132
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 185 (accept_3_2 49 132
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 48 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 132 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 185 (accept_3_2 46 132 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 185 (Polychromatic418967fa.accept_7_2_6_3_1_100
  44 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 185 (accept_3_2 43
  132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 185
  (Polychromatic418967fa.accept_17_8_13_15_1_2143 42 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 185 (Polychromatic418967fa.accept_19_3_18_14_1_5020 41 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 185 (accept_3_2 40 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 185 (accept_3_2 37 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 185 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 185 (accept_3_2 34 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 185 (accept_3_2 31 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 185 (accept_3_2 28 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 185 (accept_3_2 25 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 185 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 185 (accept_3_2 22 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 185 (accept_3_2 19 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 185 (accept_3_2 16 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 185 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 132 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 185
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 185 (accept_3_2 13 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 185 (accept_3_2 10 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 185 (accept_3_2 7 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 185 (accept_3_2 4 132 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 132 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 185 (accept_3_2 1 132 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 131 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 131 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 131
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 185 (accept_3_2 52 131
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 185 (accept_3_2 49 131 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 131 185 (Polychromatic418967fa.accept_17_14_12_15_1_5558 48 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 185 (accept_3_2 46 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 185 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 185 (accept_3_2 43 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 185
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 185 (accept_3_2 40 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 185 (accept_3_2 37 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 185
  (Polychromatic418967fa.accept_17_1_12_15_1_1263 35 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 131 185 (accept_3_2 34 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 131 185 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 131 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 185 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 131
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 185 (accept_3_2 31 131
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 185 (accept_3_2 28 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 185 (Polychromatic418967fa.accept_24_3_11_17_1_10650 27 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 185 (accept_3_2 25 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 131
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 185 (accept_3_2 22 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 185 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 185 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 185 (accept_3_2 19 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 185
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 185 (accept_3_2 16 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 185 (accept_3_2 13 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 185 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 185
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 185 (accept_3_2 10 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 185 (accept_3_2 7 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 185
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 185 (accept_3_2 4 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 185 (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 131 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 185 (accept_3_2 1 131 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 185))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 130 185
  (Eq.refl Bool.true) (allA_of_3_0 56 130 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 129 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 185 (accept_3_2 55 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 185 (accept_3_2 52 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 185 (accept_3_2 49 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 185 (accept_3_2 46 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 185 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 185 (accept_3_2 43 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 185 (accept_3_2 40 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 185 (accept_3_2 37 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 185 (accept_3_2 34 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 185 (accept_3_2 31 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 129 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 185 (accept_3_2 28 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 185 (accept_3_2 25 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 185
  (Polychromatic418967fa.accept_19_4_15_14_1_10614 23 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 185 (accept_3_2 22 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 129 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 129 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 185 (accept_3_2 19 129 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 185 (Polychromatic418967fa.accept_15_3_9_5_1_2082
  18 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 185 (accept_3_2 16 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 185 (accept_3_2 13 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 129 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 185 (accept_3_2 10 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 185 (accept_3_2 7 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 129 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 185
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 185 (accept_3_2 4 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 185 (accept_3_2 1 129 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 128 185
  (Eq.refl Bool.true) (allA_succ_of_accept 57 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 185
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 128 185 (accept_3_2 55 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 128 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 128 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 185 (accept_3_2 52 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 185 (accept_3_2 49 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 185 (accept_3_2 46 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 185 (accept_3_2 43 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 185 (accept_3_2 40 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 185
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 185 (accept_3_2 37 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 128 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 185 (accept_3_2 34 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 185 (accept_3_2 31 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 185 (accept_3_2 28 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 185 (accept_3_2 25 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 185 (accept_3_2 22 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 185 (accept_3_2 19 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 185 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 185 (accept_3_2 16 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 185 (accept_3_2 13 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 185 (accept_3_2 10 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 185 (accept_3_2 7 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 185 (accept_3_2 4 128 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 185 (accept_3_2 1 128 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 127 185 (Eq.refl Bool.true) (allA_of_3_0
  59 127 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 126 185 (Eq.refl Bool.true) (allA_succ_of_accept 59
  126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 126 185 (accept_3_2 58 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 126 185 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 126 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 185 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 126
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 185 (accept_3_2 55 126
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 126 185 (Polychromatic418967fa.accept_16_5_14_9_1_2572 53 126 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 185 (accept_3_2 52 126 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 185
  (Polychromatic418967fa.accept_20_10_6_5_1_7776 50 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 185 (accept_3_2 49 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 126 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 185 (accept_3_2 46 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 185 (accept_3_2 43 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 126 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 126 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 185 (accept_3_2 40 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 185
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 38 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 185 (accept_3_2 37 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 126 185 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 185 (accept_3_2 34 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 185 (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 185
  (Polychromatic418967fa.accept_13_6_9_3_1_915 32 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 185 (accept_3_2 31 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 126 185 (Polychromatic418967fa.accept_20_10_6_5_1_7776 30 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 185 (accept_3_2 28 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 185
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 185 (accept_3_2 25 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 185 (accept_3_2 22 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 185
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 185 (accept_3_2 19 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 185 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 185 (Polychromatic418967fa.accept_19_17_12_14_1_3655 17 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 185 (accept_3_2 16 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 185 (accept_3_2 13 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 185 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 185 (accept_3_2 10 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 185
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 185 (accept_3_2 7 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 185 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 185 (accept_3_2 4 126 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 185
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 185 (accept_3_2 1 126 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 125 185 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 125 185 5 12 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 125 185 (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 125 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 185 (accept_3_2 58 125 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 125 185 5 11 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 125 185 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 125 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 185 (accept_3_2 52 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 125 185 5 10 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 125 185 (accept_3_2 49 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 125 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 185 (accept_3_2 46 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 125 185 5 9 25 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 125 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 185 (accept_3_2 43 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 185 (Polychromatic418967fa.accept_19_3_11_14_1_7838 41 125 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 185 5 8 25 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 185 (accept_3_2 37 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 125 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 185 5 7 25 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 185 (accept_3_2 34 125 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 185 (accept_3_2 31 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 185 5 6 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 185 (accept_3_2 28 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 185 (Polychromatic418967fa.accept_22_5_15_9_1_10649 27 125 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 185
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 125 185 5 5 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 125 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 185 (accept_3_2 22 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 185 5 4 25 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 185 (accept_3_2 19
  125 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 185 (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 185 (accept_3_2 16 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 125 185 5 3 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 125 185 (Polychromatic418967fa.accept_17_14_6_15_1_3151 14 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 185 (accept_3_2 13 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 185 (Polychromatic418967fa.accept_8_4_5_1_1_299
  12 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 125 185 5 2 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 125 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 185 (Polychromatic418967fa.accept_17_8_6_15_1_523 8 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 185 (accept_3_2 7 125 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 185 5 1 25 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 185 (accept_3_2 4
  125 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 185
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 125 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 125 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 185 (accept_3_2 1 125 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 125 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 124 185
  (Eq.refl Bool.true) (allA_of_3_0 62 124 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 123 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 185 (accept_3_2 61 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 185 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 123 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 185
  (Polychromatic418967fa.accept_11_4_2_9_1_496 59 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 185 (accept_3_2 58 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 185 (accept_3_2 55 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 185 (accept_3_2 52 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 185 (accept_3_2 49 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 185 (accept_3_2 46 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 185 (accept_3_2 43 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 185 (accept_3_2 40 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 185 (accept_3_2 37 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 185 (accept_3_2 34 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 185 (accept_3_2 31 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 185 (accept_3_2 28 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 185 (accept_3_2 25 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 185
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 185 (accept_3_2 22 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 185 (accept_3_2 19 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 185 (accept_3_2 16 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 185 (accept_3_2 13 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 185 (accept_3_2 10 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 185 (accept_3_2 7 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 185
  (Polychromatic418967fa.accept_13_5_6_3_1_868 5 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 185 (accept_3_2 4 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 185 (accept_3_2 1 123 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  122 185 (Eq.refl Bool.true) (allA_succ_of_accept 63 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 185
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 185 (accept_3_2 61 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 185 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 185 (accept_3_2 58 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 185 (accept_3_2 55 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 185 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 185 (accept_3_2 52 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 185
  (Polychromatic418967fa.accept_13_11_5_3_1_889 50 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 185 (accept_3_2 49 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 185 (accept_3_2 46 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 185 (accept_3_2 43 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 185 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 185 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 185 (accept_3_2 40 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 185 (accept_3_2 37 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 185 (Polychromatic418967fa.accept_23_13_7_1_1_10648 36 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 185 (accept_3_2 34 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 185
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 185 (accept_3_2 31 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 185 (Polychromatic418967fa.accept_20_10_2_5_1_10647 30 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 185 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 185 (accept_3_2 28 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 185
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 185 (accept_3_2 25 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 185 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 185 (accept_3_2 22 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 185 (accept_3_2 19 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 185 (accept_3_2 16 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 185
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 185 (accept_3_2 13 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 185 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 185 (accept_3_2 10 122 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 185 (accept_3_2 7 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 185 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 185 (Polychromatic418967fa.accept_19_5_8_14_1_6384 5 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 185 (accept_3_2 4 122 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 185
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 185 (accept_3_2 1 122 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 121 185 (Eq.refl Bool.true)
  (allA_of_3_0 65 121 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 120 185 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 120 185 5 13 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 120 185 (accept_3_2 64 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 120 185 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 185 (accept_3_2 61 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 185 5 12 24 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 185
  (Polychromatic418967fa.accept_25_9_20_10_1_10646 59 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 120 185 (accept_3_2 58 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 120 185 (Polychromatic418967fa.accept_22_13_10_9_1_10645 57 120 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 56
  120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 120 185 5 11 24 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 120 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 185 (accept_3_2 52 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 185 5 10 24 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 185 (accept_3_2 49 120 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 185 (Polychromatic418967fa.accept_19_10_6_14_1_4959 48 120
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 120 185 (accept_3_2 46 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  120 185 5 9 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 120 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 120 185 (accept_3_2 43 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 120 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 185 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 120
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 185 5 8 24 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 185 (accept_3_2 37 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 185 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 120 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 120 185 5 7 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 185 (accept_3_2 34 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 185 (Polychromatic418967fa.accept_7_5_1_3_1_103
  33 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 185 (accept_3_2 31 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  120 185 5 6 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 120 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 120 185 (accept_3_2 28 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 120 185 (Polychromatic418967fa.accept_18_9_12_5_1_864 27 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 120 185 5 5 24 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 120 185
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 185 (accept_3_2 22 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 185 (Polychromatic418967fa.accept_22_21_10_9_1_2681 21 120 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 185 5 4 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 185 (accept_3_2 19 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 185 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 185 (accept_3_2 16 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  120 185 5 3 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 120 185 (Polychromatic418967fa.accept_21_14_15_17_1_2972 14 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 185 (accept_3_2 13 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 120 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 185 5 2 24 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 185 (accept_3_2 7 120 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 120 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 120 185 5 1 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 185 (accept_3_2 4 120 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 185 (Polychromatic418967fa.accept_17_3_1_15_1_6835 3 120 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 185 (accept_3_2 1 120 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 119 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 185 (Polychromatic418967fa.accept_19_8_5_14_1_3586 65 119
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 185 (accept_3_2 64 119
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 185
  (Polychromatic418967fa.accept_13_11_2_3_1_883 63 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 119 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 185 (accept_3_2 61 119 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 119 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 185
  (Polychromatic418967fa.accept_19_2_5_14_1_10644 59 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 119 185 (accept_3_2 58 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 119 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 119
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 185 (accept_3_2 55 119
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2
  54 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 185 (accept_3_2 52 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 185 (accept_3_2 49 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 185
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 185 (accept_3_2 46 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 185 (Polychromatic418967fa.accept_16_13_7_9_1_2606 45 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 185 (accept_3_2 43 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 185 (accept_3_2 40 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 185 (accept_3_2 37 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 185 (accept_3_2 34 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 185 (Polychromatic418967fa.accept_14_4_7_3_1_1718 32 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 185 (accept_3_2 31 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 185
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 185 (accept_3_2 28 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 185 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 185 (accept_3_2 25 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 185
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 185 (accept_3_2 22 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 185 (Polychromatic418967fa.accept_21_20_14_17_1_10643 20 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 185 (accept_3_2 19 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 185 (accept_3_2 16 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 185 (accept_3_2 13 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 185 (accept_3_2 10 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 185 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 185 (accept_3_2 7 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 185
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 185 (accept_3_2 4 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 185 (accept_3_2 1 119 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 118 185 (Eq.refl Bool.true) (allA_of_3_0 68 118 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 117 185
  (Eq.refl Bool.true) (allA_succ_of_accept 68 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 185 (accept_3_2 67 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 117
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 185 (accept_3_2 64 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 185 (accept_3_2 61 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 185
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 59 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 185 (accept_3_2 58 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 185 (accept_3_2 55 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 185 (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 117 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 185 (accept_3_2 52 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 185 (accept_3_2 49 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 185
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 47 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 185 (accept_3_2 46 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 185 (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 185 (accept_3_2 43 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 185
  (Polychromatic418967fa.accept_23_18_2_1_1_10642 41 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 117 185 (accept_3_2 40 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 117 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 185 (accept_3_2 37 117 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 185 (Polychromatic418967fa.accept_7_1_5_3_1_268
  36 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 185
  (Polychromatic418967fa.accept_11_2_7_9_1_890 35 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 185 (accept_3_2 34 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 185 (accept_3_2 31 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 185 (accept_3_2 28 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 185 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 185 (accept_3_2 25 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 185 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 185 (accept_3_2 22 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 185 (accept_3_2 19 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 185
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 185 (accept_3_2 16 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 185 (accept_3_2 13 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 185
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 185 (accept_3_2 10 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 185 (accept_3_2 7 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 117 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 185
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 185 (accept_3_2 4 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 185 (accept_3_2 1 117 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 116 185 (Eq.refl Bool.true) (allA_succ_of_accept 69 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32
  69 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 185
  (Polychromatic418967fa.accept_15_8_11_5_1_169 68 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 116 185 (accept_3_2 67 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 116 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 116 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 185 (accept_3_2 64 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 116 185 (accept_3_2 61 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 116 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 116 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 185 (accept_3_2 58 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 185 (accept_3_2 55 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 185 (accept_3_2 52 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 185 (accept_3_2 49 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 185 (accept_3_2 46 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 185 (accept_3_2 43 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 185 (accept_3_2 40 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 185 (accept_3_2 37 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 185 (accept_3_2 34 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 185 (accept_3_2 31 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 185 (accept_3_2 28 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 185 (accept_3_2 25 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 185 (accept_3_2 22 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 185 (accept_3_2 19 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 185 (Polychromatic418967fa.accept_20_18_16_5_1_9137 18 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 185 (accept_3_2 16 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 185 (accept_3_2 13 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 185 (accept_3_2 10 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 185 (accept_3_2 7 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 185 (accept_3_2 4 116 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 185 (accept_3_2 1 116 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 115 185 (Eq.refl Bool.true)
  (allA_of_3_0 71 115 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 114 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 185 (accept_3_2 70 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 114 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 185 (Polychromatic418967fa.accept_7_5_2_3_1_106
  68 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 185 (accept_3_2 67
  114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 66 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 185 (accept_3_2 64 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 185 (Polychromatic418967fa.accept_7_6_2_3_1_107
  62 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 185 (accept_3_2 61
  114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 185
  (Polychromatic418967fa.accept_16_12_2_9_1_3461 60 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 185 (accept_3_2 58 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 114 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 185 (Polychromatic418967fa.accept_9_2_6_5_1_227
  56 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 185 (accept_3_2 55
  114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 185 (accept_3_2 52 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 185 (Polychromatic418967fa.accept_7_1_2_3_1_257
  50 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 185 (accept_3_2 49
  114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 185 (accept_3_2 46 114 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 185 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 185 (accept_3_2 43 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 185 (accept_3_2 40 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 185 (accept_3_2 37 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 185 (accept_3_2 34 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 185
  (Polychromatic418967fa.accept_13_6_10_3_1_897 32 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 185 (accept_3_2 31 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 185 (accept_3_2 28 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 185 (accept_3_2 25 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 185 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 185 (accept_3_2 22 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 185 (accept_3_2 19 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 185 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 185 (accept_3_2 16 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 185
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 185 (accept_3_2 13 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 185 (accept_3_2 10 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 185 (accept_3_2 7 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 185 (accept_3_2 4 114 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 185 (accept_3_2 1 114 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 113 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 113 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 113
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 185 (accept_3_2 70 113
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 185
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 69 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 113 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 113 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 185 (accept_3_2 67 113 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 113 185 (Polychromatic418967fa.accept_16_2_1_9_1_2577 66 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 185 (accept_3_2 64 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 185 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 62 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 185 (accept_3_2 61 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 185
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 59 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 185 (accept_3_2 58 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 185 (accept_3_2 55 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 185 (accept_3_2 52 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 50 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 185 (accept_3_2 49 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 113
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 185 (accept_3_2 46 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 185 (accept_3_2 43 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 185
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 185 (accept_3_2 40 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 185 (accept_3_2 37 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 185 (Polychromatic418967fa.accept_21_15_8_17_1_7436 36 113
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 185
  (Polychromatic418967fa.accept_19_16_18_14_1_3562 35 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 113 185 (accept_3_2 34 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 113 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 185 (accept_3_2 31 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102
  30 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 185
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 185 (accept_3_2 28 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 185 (accept_3_2 25 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 185 (Polychromatic418967fa.accept_16_8_1_9_1_847 24 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 185 (accept_3_2 22 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 185 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 185 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 185 (accept_3_2 19 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 185 (accept_3_2 16 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 185 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 185 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 185 (accept_3_2 13 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 185 (accept_3_2 10 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 185 (accept_3_2 7 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 113 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 185 (accept_3_2 4 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 185 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 113 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 185 (accept_3_2 1 113 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 112 185 (Eq.refl Bool.true) (allA_of_3_0 74 112 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 111 185 (Eq.refl Bool.true) (allA_succ_of_gcd 74 111 185 37 2 3 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 111 185 (accept_3_2 73 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 185 (accept_3_2 70 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 185 (accept_3_2 67 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 185 (accept_3_2 64 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 185 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 185 (accept_3_2 61 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 185 (accept_3_2 58 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 185 (accept_3_2 55 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 185 (accept_3_2 52 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 185 (accept_3_2 49 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 185 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 185 (accept_3_2 46 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 185 (accept_3_2 43 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 185
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 185 (accept_3_2 40 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 37 111 185 37 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 36 111 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  36 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 185 (accept_3_2 34 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 185 (accept_3_2 31 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 185 (accept_3_2 28 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 185 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 185 (accept_3_2 25 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 185 (accept_3_2 22 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 185 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 185 (accept_3_2 19 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 185 (accept_3_2 16 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 185 (accept_3_2 13 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 111 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 185 (accept_3_2 10 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 185 (accept_3_2 7 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 185
  (Polychromatic418967fa.accept_19_5_16_14_1_2374 5 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 185 (accept_3_2 4 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 111 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 185 (accept_3_2 1 111 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 110 185 (Eq.refl Bool.true) (allA_succ_of_gcd 75 110 185 5 15 22 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 110 185
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 74 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 110 185 (accept_3_2 73 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 110 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 185 5 14 22 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 110 185 (Polychromatic418967fa.accept_12_8_2_5_1_844 68 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 185 (accept_3_2 67 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 110 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 110 185 5 13 22 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 110 185 (accept_3_2 64 110 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 185 (accept_3_2 61 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  110 185 5 12 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 185 (accept_3_2 58 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 110 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 185 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 110 185 5 11 22 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 110 185
  (Polychromatic418967fa.accept_20_14_10_5_1_2117 54 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 185 (accept_3_2 52 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 185 5 10 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 185 (accept_3_2 49 110 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 185 (Polychromatic418967fa.accept_9_3_2_5_1_234
  48 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 185 (accept_3_2 46 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  110 185 5 9 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 110 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 110 185 (accept_3_2 43 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 110 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 185 (Polychromatic418967fa.accept_20_1_10_5_1_6044 41 110
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 185 5 8 22 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 110 185 (Polychromatic418967fa.accept_20_18_10_5_1_3306 38 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 185 (accept_3_2 37 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 110 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 110 185 5 7 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 110 185 (accept_3_2 34 110 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 185 (accept_3_2 31 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  110 185 5 6 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 110 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 110 185 (accept_3_2 28 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 110 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 110 185 5 5 22 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 185
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 185 (accept_3_2 22 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 110 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 185 5 4 22 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 185 (accept_3_2 19 110 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 185 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 110
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 185 (accept_3_2 16 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  110 185 5 3 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 110 185 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 110 185 (accept_3_2 13 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 185 5 2 22 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 185 (accept_3_2 7 110 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 185 5 1 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 185 (accept_3_2 4 110 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 185 (accept_3_2 1 110 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 109 185 (Eq.refl
  Bool.true) (allA_of_3_0 77 109 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 108 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 108 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 185 (accept_3_2 76 108 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 108 185 (Polychromatic418967fa.accept_19_18_13_14_1_4995 75 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 185
  (Polychromatic418967fa.accept_20_14_8_5_1_6090 74 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 185 (accept_3_2 73 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 108 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 108 185 (Polychromatic418967fa.accept_21_8_3_17_1_7399 71 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 185 (accept_3_2 70 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 108 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 185
  (Polychromatic418967fa.accept_15_8_3_5_1_608 68 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 185 (accept_3_2 67 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 185 (Polychromatic418967fa.accept_13_1_4_3_1_1545 66 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 185 (Polychromatic418967fa.accept_17_14_6_15_1_3151 65 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 185 (accept_3_2 64 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 108
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 185 (accept_3_2 61 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 185 (Polychromatic418967fa.accept_17_9_6_15_1_5454 60 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 185 (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 185 (accept_3_2 58 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 108
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 185
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 185 (accept_3_2 55 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 185 (accept_3_2 52 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 185 (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 108 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 185
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 50 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 185 (accept_3_2 49 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 185 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 185 (accept_3_2 46 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 185
  (Polychromatic418967fa.accept_21_2_3_17_1_7398 44 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 185 (accept_3_2 43 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 185 (Polychromatic418967fa.accept_14_13_10_3_1_1037 41 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 185 (accept_3_2 40 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 108
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 185
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 38 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 185 (accept_3_2 37 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 108 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 108 185 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 185 (accept_3_2 34 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 108
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 185 (accept_3_2 31 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 185 (Polychromatic418967fa.accept_20_10_8_5_1_7735 30 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 185 (accept_3_2 28 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 185
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 185 (accept_3_2 25 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 185 (accept_3_2 22 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 185
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 185 (accept_3_2 19 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 185 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 185 (accept_3_2 16 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 185 (Polychromatic418967fa.accept_19_15_13_14_1_5015 15
  108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 185
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 185 (accept_3_2 13 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 185 (Polychromatic418967fa.accept_22_11_20_9_1_10641 11 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 185 (accept_3_2 10 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 108 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 185
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 185 (accept_3_2 7 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 185 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 185 (accept_3_2 4 108 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 185 (accept_3_2 1 108 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 107 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 185
  (Polychromatic418967fa.accept_21_14_2_17_1_758 77 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 185 (accept_3_2 76 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 185 (accept_3_2 73 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 185 (accept_3_2 70 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 185 (accept_3_2 67 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 185 (accept_3_2 64 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 185 (accept_3_2 61 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 185
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 185 (accept_3_2 58 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 185 (accept_3_2 55 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 185 (accept_3_2 52 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 185 (accept_3_2 49 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 185 (accept_3_2 46 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 185 (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 185 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 185 (accept_3_2 43 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 185 (accept_3_2 40 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 185 (accept_3_2 37 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 185
  (Polychromatic418967fa.accept_19_16_12_14_1_10640 35 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 107 185 (accept_3_2 34 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 107 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 107
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 185 (accept_3_2 31 107
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 185 (accept_3_2 28 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 185 (accept_3_2 25 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 185 (accept_3_2 22 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 185 (accept_3_2 19 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 185
  (Polychromatic418967fa.accept_19_17_12_14_1_3655 17 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 185 (accept_3_2 16 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 185 (accept_3_2 13 107 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 185 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 185 (accept_3_2 10 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 185 (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 185 (accept_3_2 7 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 185 (accept_3_2 4 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 107 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 185 (accept_3_2 1 107 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 106 185 (Eq.refl Bool.true) (allA_of_3_0 80 106 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 105 185 (Eq.refl Bool.true) (allA_succ_of_gcd 80 105 185 5 16 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 185 (accept_3_2 79 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 185 (Polychromatic418967fa.accept_18_6_15_5_1_6563 78 105
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 185
  (Polychromatic418967fa.accept_19_1_10_14_1_3597 77 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 105 185 (accept_3_2 76 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 185 5 15 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 185 (accept_3_2 73 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 185 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 105 185 5 14 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 105 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 185 (accept_3_2 67 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 105 185 5 13 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 105 185 (accept_3_2 64 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 185 (accept_3_2 61 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 185 5 12 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 185
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 185 (accept_3_2 58 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 185 5 11 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 185
  (Polychromatic418967fa.accept_13_2_1_3_1_419 54 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 185 (accept_3_2 52 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 185 5 10 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 185 (accept_3_2 49 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 48
  105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 185 (accept_3_2 46 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  105 185 5 9 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 185 (accept_3_2 43 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 185 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 185 (Polychromatic418967fa.accept_13_2_1_3_1_419 41 105
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 185 5 8 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 185 (accept_3_2 37 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 185 5 7 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 185 (accept_3_2 34 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 185 (Polychromatic418967fa.accept_13_7_1_3_1_1523
  33 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 185 (accept_3_2 31 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  105 185 5 6 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 105 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 105 185 (accept_3_2 28 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 105 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 185 5 5 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 185
  (Polychromatic418967fa.accept_13_11_1_3_1_910 24 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 185 (Polychromatic418967fa.accept_19_4_10_14_1_7833 23 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 185 (accept_3_2 22 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 185 5 4 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 185 (accept_3_2 19 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 185 (Polychromatic418967fa.accept_13_5_1_3_1_878
  18 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 185 (accept_3_2 16 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  105 185 5 3 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 185 (accept_3_2 13 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 185 5 2 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 105 185
  (Polychromatic418967fa.accept_18_9_15_5_1_6551 9 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 185 (accept_3_2 7 105 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 185 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 185 5 1 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 185 (accept_3_2 4 105 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 185 (accept_3_2 1 105 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 104 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 104 185
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 80 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 104 185 (accept_3_2 79 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 104 185 (Polychromatic418967fa.accept_17_10_2_15_1_3179 78 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 104 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 104 185 (accept_3_2 76 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 185 (accept_3_2 73 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 104 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 185 (accept_3_2 70 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 185
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 68 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 185 (accept_3_2 67 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 185 (accept_3_2 64 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 185
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 185 (accept_3_2 61 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 59 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 185 (accept_3_2 58 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 185
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 185 (accept_3_2 55 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 185 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 185 (accept_3_2 52 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 185 (accept_3_2 49 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 185 (Polychromatic418967fa.accept_22_4_16_9_1_10639 48 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 185 (accept_3_2 46 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 185 (accept_3_2 43 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 185 (Polychromatic418967fa.accept_19_4_9_14_1_1345 42 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 185 (accept_3_2 40 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 185 (accept_3_2 37 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 185 (Polychromatic418967fa.accept_19_16_9_14_1_10638 35 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 185 (accept_3_2 34 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 185 (accept_3_2 31 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 185 (accept_3_2 28 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 185
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 185 (accept_3_2 25 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 185 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 185 (accept_3_2 22 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 185
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 185 (accept_3_2 19 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 185 (accept_3_2 16 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 185 (accept_3_2 13 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 185 (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 185 (accept_3_2 10 104 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 185
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 185 (accept_3_2 7 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 185 (Polychromatic418967fa.accept_19_5_9_14_1_3505 5 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 185 (accept_3_2 4 104 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 185 (accept_3_2 1 104 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 103 185 (Eq.refl
  Bool.true) (allA_of_3_0 83 103 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 102 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 102 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 185 (accept_3_2 82 102 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 81 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 185 (accept_3_2 79 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 77 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 185 (accept_3_2 76 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 185 (accept_3_2 73 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 185 (accept_3_2 70 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 185 (accept_3_2 67 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 185 (Polychromatic418967fa.accept_13_1_11_3_1_901 66 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 185 (accept_3_2 64 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 185 (accept_3_2 61 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 102 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 185 (accept_3_2 58 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 185 (accept_3_2 55 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 185 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 185 (accept_3_2 52 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 185 (accept_3_2 49 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 185 (accept_3_2 46 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 185 (Polychromatic418967fa.accept_16_13_6_9_1_2561 45 102 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 185 (accept_3_2 43 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 185 (accept_3_2 40 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 185 (accept_3_2 37 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 185 (accept_3_2 34 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 185
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 185 (accept_3_2 31 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 185 (Polychromatic418967fa.accept_19_11_7_14_1_6394 30 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 185 (accept_3_2 28 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 185 (accept_3_2 25 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 185 (accept_3_2 22 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 185 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 102 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 185 (accept_3_2 19 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 185 (accept_3_2 16 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 185
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 185 (accept_3_2 13 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 185 (Polychromatic418967fa.accept_19_12_7_14_1_10637 12 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 185 (accept_3_2 10 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 185 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 102
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 185 (accept_3_2 7 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 185 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 185 (accept_3_2 4 102 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 185 (accept_3_2 1 102 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 101 185
  (Eq.refl Bool.true) (allA_succ_of_accept 84 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 185
  (Polychromatic418967fa.accept_15_8_11_5_1_169 83 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 185 (accept_3_2 82 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 81 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 185 (accept_3_2 79 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 185 (accept_3_2 76 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 74 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 185 (accept_3_2 73 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 185 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 101
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 185 (accept_3_2 70 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 185 (accept_3_2 67 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 185
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 65 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 185 (accept_3_2 64 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 185 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 185 (accept_3_2 61 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 185 (accept_3_2 58 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 185 (accept_3_2 55 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 101
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 185 (accept_3_2 52 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 185 (Polychromatic418967fa.accept_13_11_10_3_1_3020 50 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 185 (accept_3_2 49 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 185 (accept_3_2 46 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 185 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 185 (accept_3_2 43 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 185
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 185 (accept_3_2 40 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 38 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 185 (accept_3_2 37 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 185 (accept_3_2 34 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 185 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 185 (accept_3_2 31 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 185 (accept_3_2 28 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 185 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 185 (accept_3_2 25 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 185
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 185 (accept_3_2 22 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 185 (accept_3_2 19 101 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 185 (accept_3_2 16 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 185 (accept_3_2 13 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 185
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 185 (accept_3_2 10 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 101 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 185 (accept_3_2 7 101 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 185
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 5 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 185 (accept_3_2 4 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 185 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 185 (accept_3_2 1 101 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 101
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 100 185
  (Eq.refl Bool.true) (allA_of_3_0 86 100 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 99 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 185 (accept_3_2 85 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 185
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 83 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 185 (accept_3_2 82 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  99 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 185 (accept_3_2 79 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 185
  (Polychromatic418967fa.accept_21_14_15_17_1_2972 77 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 99 185 (accept_3_2 76 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 99 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 185 (accept_3_2 73 99 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 72
  99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 185 (accept_3_2 70 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  99 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 185 (accept_3_2 67 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 185 (accept_3_2 64 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  99 185 (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 185 (accept_3_2 61 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 185
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 185 (accept_3_2 58 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  99 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 185 (accept_3_2 55 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 185 (accept_3_2 52 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 185 (accept_3_2 49 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 185 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 185 (accept_3_2 46 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 185 (accept_3_2 43 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 185 (accept_3_2 40 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 185 (accept_3_2 37 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 185
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 185 (accept_3_2 34 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 185 (accept_3_2 31 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 185
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 185 (accept_3_2 28 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 185 (accept_3_2 25 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 185 (accept_3_2 22 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 185 (accept_3_2 19 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 185
  (Polychromatic418967fa.accept_22_17_11_9_1_10636 17 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 99 185 (accept_3_2 16 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 99 185 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 99 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 185 (accept_3_2 13 99 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 185 (accept_3_2 10 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 185 (accept_3_2 7 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 185 (accept_3_2 4 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  185 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 99 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 99 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 185 (accept_3_2 1 99 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 99
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 98 185
  (Eq.refl Bool.true) (allA_succ_of_accept 87 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 185
  (Polychromatic418967fa.accept_13_8_7_3_1_430 86 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 185 (accept_3_2 85 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 185 (accept_3_2 82 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 185 (accept_3_2 79 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 185 (accept_3_2 76 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 185 (accept_3_2 73 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 185 (accept_3_2 70 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 185 (accept_3_2 67 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 185 (accept_3_2 64 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 185 (accept_3_2 61 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 185 (accept_3_2 58 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 185 (accept_3_2 55 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 185 (Polychromatic418967fa.accept_16_6_2_9_1_5897 54 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 185 (Polychromatic418967fa.accept_10_3_8_5_1_606 53 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 185 (accept_3_2 52 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 185
  (Polychromatic418967fa.accept_13_11_7_3_1_894 50 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 185 (accept_3_2 49 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 185 (accept_3_2 46 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 185 (accept_3_2 43 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 185 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 185 (accept_3_2 40 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 185 (accept_3_2 37 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 185 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 185 (accept_3_2 34 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 185 (accept_3_2 31 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 185 (accept_3_2 28 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 185
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 185 (accept_3_2 25 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 185 (accept_3_2 22 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 185 (accept_3_2 19 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 185 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 185 (accept_3_2 16 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 185
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 185 (accept_3_2 13 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 185 (accept_3_2 10 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 185
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 185 (accept_3_2 7 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 185 (Polychromatic418967fa.accept_17_5_13_15_1_5464 5 98 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 185 (accept_3_2 4 98 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 185 (accept_3_2 1 98 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 97 185
  (Eq.refl Bool.true) (allA_of_3_0 89 97 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 96 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 96 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 185 (accept_3_2 88 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 96 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 87 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 86 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 96 185 (accept_3_2 85 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 96 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 185 (accept_3_2 82 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 96 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 81 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 185 (accept_3_2 79 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 96 185 (Polychromatic418967fa.accept_22_11_8_9_1_10635 77 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 185 (accept_3_2 76 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 185 (accept_3_2 73 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 185 (accept_3_2 70 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 96 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 185
  (Polychromatic418967fa.accept_21_5_12_17_1_10634 68 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 96 185 (accept_3_2 67 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 96 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 185 (accept_3_2 64 96 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 96 185 (Polychromatic418967fa.accept_13_11_5_3_1_889
  63 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 185 (accept_3_2 61 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  96 185 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 96 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 185 (accept_3_2 58 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 185 (accept_3_2 55 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  96 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 185 (accept_3_2 52 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 185 (accept_3_2 49 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 185 (accept_3_2 46 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 185 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 185 (accept_3_2 43 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 185 (accept_3_2 40 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 185 (accept_3_2 37 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 185 (accept_3_2 34 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 185 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 185
  (Polychromatic418967fa.accept_11_10_8_9_1_492 32 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 185 (accept_3_2 31 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 185 (accept_3_2 28 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 185 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 185 (accept_3_2 25 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 185 (accept_3_2 22 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 185 (accept_3_2 19 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 185 (accept_3_2 16 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 185 (accept_3_2 13 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 185 (accept_3_2 10 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 185 (accept_3_2 7 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  185 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 96 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 185 (Polychromatic418967fa.accept_14_5_12_3_1_3397 5 96 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 185 (accept_3_2 4 96 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 185 (accept_3_2 1 96 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 95 185
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 95 185 5 18 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 95 185 (Polychromatic418967fa.accept_17_4_10_15_1_5444 89 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 185 (accept_3_2 88 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 185 (Polychromatic418967fa.accept_17_2_10_15_1_1238 87 95
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 185 5 17 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 185 (Polychromatic418967fa.accept_20_4_15_5_1_10633 84 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 185 (accept_3_2 82 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 185 (Polychromatic418967fa.accept_20_1_15_5_1_9135
  81 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 185 5 16 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 185 (accept_3_2 79
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 185 (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 185 (accept_3_2 76 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 95 185 5 15 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 185 (accept_3_2 73 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 185 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 185 5 14 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 185 (Polychromatic418967fa.accept_11_2_7_9_1_890 68 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 185 (accept_3_2 67 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 185 5 13 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 185 (accept_3_2 64
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 185
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 185 (accept_3_2 61 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 185 5 12 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 185 (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 185 (accept_3_2 58 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 185
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 56 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 185 5 11 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 185 (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 185 (accept_3_2 52 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 185 (Polychromatic418967fa.accept_13_12_4_3_1_1528
  51 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 185 5 10 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 185 (accept_3_2 49
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 185 (Polychromatic418967fa.accept_20_7_15_5_1_6087 47 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 185 (accept_3_2 46 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 185 5 9 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 185 (Polychromatic418967fa.accept_20_4_15_5_1_10633 44 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 185 (accept_3_2 43 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 185 5 8 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 185 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 185 (accept_3_2 37 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 185 5 7 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 185 (accept_3_2 34
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 185
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 185 (Polychromatic418967fa.accept_20_12_15_5_1_9169 32 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 185 (accept_3_2 31 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 185 5 6 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 185 (accept_3_2 28 95 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 185 5 5 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 185 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 185 (Polychromatic418967fa.accept_20_3_15_5_1_10631 23 95
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 185 (accept_3_2 22 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 185 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  21 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 185 5 4 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 185 (accept_3_2 19
  95 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 185 (Polychromatic418967fa.accept_20_17_15_5_1_4627 17 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 185 (accept_3_2 16 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 185 5 3 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 185 (accept_3_2 13 95 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 185 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 95 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 185
  (Polychromatic418967fa.accept_20_11_15_5_1_10632 11 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 95 185 5 2 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 95 185 (Polychromatic418967fa.accept_20_9_15_5_1_4670 9 95 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 185 (accept_3_2 7 95 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 185 5 1 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 185 (accept_3_2 4 95
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 185
  (Polychromatic418967fa.accept_20_3_15_5_1_10631 3 95 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 185 (accept_3_2 1 95 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 94 185
  (Eq.refl Bool.true) (allA_of_3_0 92 94 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 185
  (allA_succ_of_accept 92 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 185 (accept_3_2 91 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 89
  93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 185 (accept_3_2 88 93
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 185
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 185 (accept_3_2 85 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 83
  93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 185 (accept_3_2 82 93
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 185
  (Polychromatic418967fa.accept_15_6_3_5_1_607 81 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 185 (accept_3_2 79 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 185 (Polychromatic418967fa.accept_10_7_3_5_1_301
  77 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 185 (accept_3_2 76
  93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 185 (accept_3_2 73 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 71
  93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 185 (accept_3_2 70 93
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 185 (accept_3_2 67 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 185 (Polychromatic418967fa.accept_13_1_2_3_1_911 66 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 65
  93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 185 (accept_3_2 64 93
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 185
  (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 185 (accept_3_2 61 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 185
  (Polychromatic418967fa.accept_19_2_17_14_1_6399 59 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 185 (accept_3_2 58 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  93 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 185 (accept_3_2 55 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 185 (accept_3_2 52 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 185 (accept_3_2 49 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 185 (accept_3_2 46 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 185 (Polychromatic418967fa.accept_21_3_9_17_1_2983 45 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 185 (accept_3_2 43 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 185 (accept_3_2 40 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 185 (accept_3_2 37 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 185 (accept_3_2 34 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 185 (accept_3_2 31 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 185 (Polychromatic418967fa.accept_17_13_8_15_1_8135 30 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 185 (accept_3_2 28 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 185 (accept_3_2 25 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 185
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 185 (accept_3_2 22 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 185 (accept_3_2 19 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 185 (accept_3_2 16 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 185 (accept_3_2 13 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 185 (accept_3_2 10 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 185 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 185 (accept_3_2 7 93 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 185 (accept_3_2 4 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 185 (accept_3_2 1 93 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 185
  (allA_succ_of_accept 91 92 185 (accept_3_2 91 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 185 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 185 (accept_3_2 88 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 185 (accept_3_2 85 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 83 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 185 (accept_3_2 82 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 185 (accept_3_2 79 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 185 (accept_3_2 76 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 185 (accept_3_2 73 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 185 (accept_3_2 70 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 185 (accept_3_2 67 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 185 (accept_3_2 64 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 185 (accept_3_2 61 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 185 (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 185 (accept_3_2 58 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 185
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 56 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 185 (accept_3_2 55 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 185 (accept_3_2 52 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 185 (accept_3_2 49 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 185 (accept_3_2 46 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 185 (accept_3_2 43 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 185 (Polychromatic418967fa.accept_13_2_1_3_1_419 41 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 185 (accept_3_2 40 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 185 (accept_3_2 37 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 185 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 185 (accept_3_2 34 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 185 (accept_3_2 31 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 185 (accept_3_2 28 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 185 (accept_3_2 25 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 185 (accept_3_2 22 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 185
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 185 (accept_3_2 19 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 185 (accept_3_2 16 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 185 (accept_3_2 13 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 185 (accept_3_2 10 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 185 (accept_3_2 7 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 185 (accept_3_2 4 92 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 185 (accept_3_2 1 92 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 185
  (allA_of_3_0 91 91 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 185 (allA_succ_of_accept 89 90 185
  (Polychromatic418967fa.accept_20_9_10_5_1_6085 89 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 185 (accept_3_2 88 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 90 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 90 185 5 17 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 90 185
  (Polychromatic418967fa.accept_11_7_2_9_1_480 84 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 185 (accept_3_2 82 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 185 5 16 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 185 (accept_3_2 79 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 185 (Polychromatic418967fa.accept_17_10_5_15_1_4332 78 90
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 185
  (Polychromatic418967fa.accept_20_17_10_5_1_7765 77 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 185 (accept_3_2 76 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90
  185 5 15 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74
  90 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 90 185 (accept_3_2 73 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 185 5 14 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 185
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 69 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 90 185 (Polychromatic418967fa.accept_20_8_10_5_1_6083 68 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 185 (accept_3_2 67 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 90 185 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 90 185 5 13 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 185 (accept_3_2 64 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 185
  (Polychromatic418967fa.accept_11_7_2_9_1_480 62 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 185 (accept_3_2 61 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90
  185 5 12 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 185 (accept_3_2 58 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 90 185 (Polychromatic418967fa.accept_20_17_10_5_1_7765 57 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 56 90
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 185 5 11 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 90 185
  (Polychromatic418967fa.accept_13_2_12_3_1_415 54 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 185 (accept_3_2 52 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 185 5 10 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 185 (accept_3_2 49 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 185 (accept_3_2 46 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90
  185 5 9 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  90 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 90 185 (accept_3_2 43 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 90 185 (Polychromatic418967fa.accept_20_2_10_5_1_6082 42 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 185 (Polychromatic418967fa.accept_13_2_12_3_1_415 41 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 185 5 8 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 90 185 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 185 (accept_3_2 37 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 90 185 (Polychromatic418967fa.accept_20_16_10_5_1_9133 36 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 90 185 5 7 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 185 (accept_3_2 34 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 185 (Polychromatic418967fa.accept_16_1_10_9_1_4645 33 90
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 185 (accept_3_2 31 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  185 5 6 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 90 185 (accept_3_2 28 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 185 5 5 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 90 185
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 185 (accept_3_2 22 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 185 (Polychromatic418967fa.accept_20_1_10_5_1_6044 21 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 185 5 4 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 185 (accept_3_2 19 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 185
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 185 (accept_3_2 16 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90
  185 5 3 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  90 185 (Polychromatic418967fa.accept_20_14_10_5_1_2117 14 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 90 185 (accept_3_2 13 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 185 (Polychromatic418967fa.accept_20_12_10_5_1_4661 12 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 185 5 2 18 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 185 (Polychromatic418967fa.accept_20_8_10_5_1_6083 8 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 185 (accept_3_2 7 90 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 185 (Polychromatic418967fa.accept_20_6_10_5_1_10630 6 90 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 90 185 5 1 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 185 (accept_3_2 4 90 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 185 (accept_3_2 1 90 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 185
  (allA_succ_of_accept 88 89 185 (accept_3_2 88 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 185 (accept_3_2 85 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 185 (accept_3_2 82 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 185 (Polychromatic418967fa.accept_13_2_11_3_1_873 80 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 185 (accept_3_2 79 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 185
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 185 (accept_3_2 76 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 185 (accept_3_2 73 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 185 (accept_3_2 70 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 185 (Polychromatic418967fa.accept_14_12_5_3_1_1011 68 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 185 (accept_3_2 67 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 185 (accept_3_2 64 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 185 (Polychromatic418967fa.accept_25_13_14_10_1_5050 63 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 185 (Polychromatic418967fa.accept_13_10_11_3_1_1518 62 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 185 (accept_3_2 61 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 89 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 185
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 185 (accept_3_2 58 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 185 (accept_3_2 55 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 185
  (Polychromatic418967fa.accept_13_1_11_3_1_901 53 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 185 (accept_3_2 52 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 185 (accept_3_2 49 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 185 (accept_3_2 46 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 185 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 185 (accept_3_2 43 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 185 (accept_3_2 40 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 185 (accept_3_2 37 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 185
  (Polychromatic418967fa.accept_19_16_13_14_1_3616 35 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 89 185 (accept_3_2 34 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 185 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 89
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 185 (accept_3_2 31 89 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 185 (accept_3_2 28 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 185 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 185 (accept_3_2 25 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 185 (accept_3_2 22 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 185 (accept_3_2 19 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 185 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 185
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 185 (accept_3_2 16 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 185 (accept_3_2 13 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 185 (accept_3_2 10 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 185 (accept_3_2 7 89 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 185
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 185 (accept_3_2 4 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 185 (accept_3_2 1 89 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 185 (allA_of_3_0 88 88 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 185
  (allA_succ_of_accept 86 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 185 (accept_3_2 85 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 83
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 185 (accept_3_2 82 87
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 185
  (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 185 (accept_3_2 79 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 185 (Polychromatic418967fa.accept_13_12_9_3_1_3047
  77 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 185 (accept_3_2 76
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 185 (accept_3_2 73 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 71
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 185 (accept_3_2 70 87
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 185
  (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 185 (accept_3_2 67 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 65
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 185 (accept_3_2 64 87
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 185 (accept_3_2 61 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 185 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 185 (Polychromatic418967fa.accept_13_7_9_3_1_1504
  59 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 185 (accept_3_2 58
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 185 (accept_3_2 55 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 185 (accept_3_2 52 87
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 185
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 185 (accept_3_2 49 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 185 (accept_3_2 46 87
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 185
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 185 (accept_3_2 43 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 185 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  41 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 185 (accept_3_2 40
  87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 185 (accept_3_2 37 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 185 (accept_3_2 34 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 185 (accept_3_2 31 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 185 (accept_3_2 28 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 185 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 185 (accept_3_2 25 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 185 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 185 (accept_3_2 22 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 185 (accept_3_2 19 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 185 (accept_3_2 16 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 185 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 185 (accept_3_2 13 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 185 (accept_3_2 10 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 185 (accept_3_2 7 87 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 185
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 185 (accept_3_2 4 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 185 (accept_3_2 1 87 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 185 (allA_succ_of_accept 85 86 185 (accept_3_2 85 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 86 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 185 (accept_3_2 82 86 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 185 (accept_3_2 79 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 185 (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 185 (accept_3_2 76 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 74 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 185 (accept_3_2 73 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 185 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 185 (accept_3_2 70 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 185 (accept_3_2 67 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 185 (Polychromatic418967fa.accept_15_6_11_5_1_168 66 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 185 (Polychromatic418967fa.accept_18_11_14_5_1_3951 65 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 185 (accept_3_2 64 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 185 (accept_3_2 61 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 185 (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 185 (accept_3_2 58 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 185 (accept_3_2 55 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 185 (accept_3_2 52 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 185 (accept_3_2 49 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 185 (accept_3_2 46 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 185 (accept_3_2 43 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 185 (Polychromatic418967fa.accept_19_4_10_14_1_7833 42 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 185 (accept_3_2 40 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 185
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 185 (accept_3_2 37 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 185 (accept_3_2 34 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 185 (accept_3_2 31 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 185 (Polychromatic418967fa.accept_20_10_6_5_1_7776 30 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 185 (accept_3_2 28 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 185 (accept_3_2 25 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 185 (accept_3_2 22 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 185 (accept_3_2 19 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 185 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 185 (accept_3_2 16 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 185 (accept_3_2 13 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 185 (accept_3_2 10 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 185 (accept_3_2 7 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 185 (accept_3_2 4 86 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 185 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  2 86 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 185 (accept_3_2 1 86
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 185
  (allA_of_3_0 85 85 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 185 (allA_succ_of_accept 83 84 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 185 (accept_3_2 82 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 185 (accept_3_2 79 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 77 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 185 (accept_3_2 76 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 185 (Polychromatic418967fa.accept_13_10_6_3_1_1515 75 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 185 (accept_3_2 73 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 72 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 185 (accept_3_2 70 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 185 (Polychromatic418967fa.accept_11_2_7_9_1_890 68 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 185 (accept_3_2 67 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 185 (accept_3_2 64 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 185 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 185 (accept_3_2 61 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 185
  (Polychromatic418967fa.accept_10_9_4_5_1_616 59 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 185 (accept_3_2 58 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 185 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 185 (accept_3_2 55 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 185 (Polychromatic418967fa.accept_22_10_18_9_1_5685 54 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 185 (accept_3_2 52 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 185 (Polychromatic418967fa.accept_20_10_4_5_1_6051 50 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 185 (accept_3_2 49 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 185 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 84 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 185 (accept_3_2 46 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 185 (accept_3_2 43 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 185
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 185 (accept_3_2 40 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 185 (accept_3_2 37 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 185 (accept_3_2 34 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 185 (Polychromatic418967fa.accept_19_13_8_14_1_4960 32 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 185 (accept_3_2 31 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 185 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 84
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 185 (accept_3_2 28 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 185 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 185 (accept_3_2 25 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 185
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 185 (accept_3_2 22 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 185 (accept_3_2 19 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 185 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 185 (accept_3_2 16 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 185 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 185 (accept_3_2 13 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 185 (accept_3_2 10 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 185 (accept_3_2 7 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 185 (accept_3_2 4 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  185 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 84 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 185 (accept_3_2 1 84 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 185
  (allA_succ_of_accept 82 83 185 (accept_3_2 82 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 185 (accept_3_2 79 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 77 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 185 (accept_3_2 76 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 185 (accept_3_2 73 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 185 (accept_3_2 70 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 68 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 185 (accept_3_2 67 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 185 (accept_3_2 64 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 185 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 185 (accept_3_2 61 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 185
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 185 (accept_3_2 58 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 185 (accept_3_2 55 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 185 (accept_3_2 52 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 185 (accept_3_2 49 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 185 (accept_3_2 46 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 185 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 185 (accept_3_2 43 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 185
  (Polychromatic418967fa.accept_13_2_5_3_1_406 41 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 185 (accept_3_2 40 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 185 (accept_3_2 37 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 185 (accept_3_2 34 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 185 (accept_3_2 31 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 185
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 185 (accept_3_2 28 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 185 (accept_3_2 25 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 185 (accept_3_2 22 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 185 (Polychromatic418967fa.accept_22_20_17_9_1_7284 20 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 185 (accept_3_2 19 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 185 (accept_3_2 16 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 185 (accept_3_2 13 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 185 (accept_3_2 10 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 185 (accept_3_2 7 83 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 185
  (Polychromatic418967fa.accept_24_5_11_17_1_7068 5 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 185 (accept_3_2 4 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 83 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 185 (accept_3_2 1 83 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 185 (allA_of_3_0 82 82 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 185
  (allA_succ_of_accept 80 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 185 (accept_3_2 79 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 185 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  77 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 185 (accept_3_2 76
  81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 185
  (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 185 (accept_3_2 73 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 185 (accept_3_2 70 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 185 (accept_3_2 67 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 185
  (Polychromatic418967fa.accept_19_8_5_14_1_3586 65 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 185 (accept_3_2 64 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 185 (accept_3_2 61 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 185 (Polychromatic418967fa.accept_19_3_5_14_1_3584 60 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 185 (accept_3_2 58 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 185 (accept_3_2 55 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 185
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 185 (accept_3_2 52 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 185 (accept_3_2 49 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 185
  (Polychromatic418967fa.accept_19_9_5_14_1_7872 47 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 185 (accept_3_2 46 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 185 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 185 (accept_3_2 43 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 185 (accept_3_2 40 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 185 (accept_3_2 37 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 185
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 185 (accept_3_2 34 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 185 (accept_3_2 31 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 185 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 185 (accept_3_2 28 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 185 (accept_3_2 25 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 185
  (Polychromatic418967fa.accept_20_3_1_5_1_4643 23 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 185 (accept_3_2 22 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 185 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 185 (accept_3_2 19 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 185
  (Polychromatic418967fa.accept_19_17_5_14_1_3587 17 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 185 (accept_3_2 16 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 185 (accept_3_2 13 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 185
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 185 (accept_3_2 10 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 185 (accept_3_2 7 81 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 185
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 185 (accept_3_2 4 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 185 (accept_3_2 1 81 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 185 (allA_succ_of_accept 79 80 185 (accept_3_2 79 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 185 (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 80
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 185 (accept_3_2 76 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 185 5 15 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 185 (accept_3_2 73 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 185 (Polychromatic418967fa.accept_17_3_12_15_1_1203 71 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 185 5 14 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 80 185 (Polychromatic418967fa.accept_18_14_8_5_1_860 68 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 185 (accept_3_2 67 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 80 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 185 5 13 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 185 (accept_3_2 64 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 185 (accept_3_2 61 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  185 5 12 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 185 (Polychromatic418967fa.accept_19_2_4_14_1_10629 59 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 80 185 (accept_3_2 58 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 80 185 5 11 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 80 185
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 54 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 80 185 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 185 (accept_3_2 52 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 185 5 10 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 185 (accept_3_2 49 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 80 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 80 185 (accept_3_2 46 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 80
  185 5 9 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  80 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 80 185 (accept_3_2 43 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 80 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 185 (Polychromatic418967fa.accept_14_13_10_3_1_1037 41 80
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 185 5 8 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 80 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 185 (accept_3_2 37 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 80 185 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 80 185 5 7 16 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 80 185 (accept_3_2 34 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 185
  (Polychromatic418967fa.accept_18_14_8_5_1_860 32 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 185 (accept_3_2 31 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  185 5 6 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 80 185 (accept_3_2 28 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 80 185 5 5 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 80 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 80 185 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 185 (accept_3_2 22 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 185 5 4 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 185 (accept_3_2 19 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 185
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 185 (accept_3_2 16 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 80
  185 5 3 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  80 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 80 185 (accept_3_2 13 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 80 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 185 5 2 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 185 (Polychromatic418967fa.accept_19_8_4_14_1_5005 8 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 185 (accept_3_2 7 80 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 185 5 1 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 185 (accept_3_2 4 80 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 185 (accept_3_2 1 80 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 185 (allA_of_3_0 79
  79 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 185 (allA_succ_of_accept 77 78 185
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 185 (accept_3_2 76 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 185 (accept_3_2 73 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 185 (accept_3_2 70 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 69 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 185 (accept_3_2 67 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 185 (accept_3_2 64 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 185 (accept_3_2 61 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 185 (accept_3_2 58 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 185 (accept_3_2 55 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 185 (accept_3_2 52 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 185 (Polychromatic418967fa.accept_19_12_2_14_1_10618 50 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 185 (accept_3_2 49 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 78 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 185 (accept_3_2 46 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 185 (Polychromatic418967fa.accept_19_7_2_14_1_3569 45 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 185 (accept_3_2 43 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 185
  (Polychromatic418967fa.accept_22_19_12_9_1_9057 41 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 185 (accept_3_2 40 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 185 (accept_3_2 37 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 185 (accept_3_2 34 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 185 (accept_3_2 31 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 185 (accept_3_2 28 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 185 (accept_3_2 25 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 185 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 185 (accept_3_2 22 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 185 (accept_3_2 19 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 185 (accept_3_2 16 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 185 (Polychromatic418967fa.accept_21_14_15_17_1_2972 14 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 185 (accept_3_2 13 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 185 (accept_3_2 10 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 185 (accept_3_2 7 78 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 78 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 185 (accept_3_2 4 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 185 (accept_3_2 1 78 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 185 (allA_succ_of_accept 76 77 185 (accept_3_2 76 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 185 (Polychromatic418967fa.accept_17_7_9_15_1_8105 75 77 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 74 77 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 185 (accept_3_2 73 77 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 185 (Polychromatic418967fa.accept_10_2_7_5_1_605
  72 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 185
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 185 (accept_3_2 70 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 69 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 185 (accept_3_2 67 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 185 (Polychromatic418967fa.accept_14_10_7_3_1_1022 66 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 185
  (Polychromatic418967fa.accept_16_1_13_9_1_2551 65 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 185 (accept_3_2 64 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 62 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 185 (accept_3_2 61 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 185
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 185 (accept_3_2 58 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 185 (Polychromatic418967fa.accept_15_12_2_5_1_3939 57 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 56 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 185 (accept_3_2 55 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 185 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 77 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 185 (accept_3_2 52 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 185 (Polychromatic418967fa.accept_19_13_1_14_1_3634 51 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 185 (Polychromatic418967fa.accept_20_10_17_5_1_9139 50 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 185 (accept_3_2 49 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 77 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 185
  (Polychromatic418967fa.accept_19_9_1_14_1_1372 47 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 185 (accept_3_2 46 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 185 (Polychromatic418967fa.accept_21_3_14_17_1_10628 45 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 185 (accept_3_2 43 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 185
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 185 (accept_3_2 40 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 185 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 38 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 185 (accept_3_2 37 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 185
  (Polychromatic418967fa.accept_13_9_12_3_1_907 35 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 185 (accept_3_2 34 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 185 (accept_3_2 31 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 185 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 185
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 185 (accept_3_2 28 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 185 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 185 (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 185 (accept_3_2 25 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 185 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 77
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 185
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 185 (accept_3_2 22 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 185 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 185 (accept_3_2 19 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 185
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 185 (accept_3_2 16 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 185 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 185 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 185 (accept_3_2 13 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 185
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 185 (accept_3_2 10 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 185 (accept_3_2 7 77 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 185 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 77 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 185
  (Polychromatic418967fa.accept_16_5_13_9_1_2594 5 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 185 (accept_3_2 4 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 77 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 77 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 185 (accept_3_2 1 77 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 185 (allA_of_3_0 76 76 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 185 (allA_succ_of_accept 74 75
  185 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 185 (accept_3_2 73 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 185 5 14 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 185
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 185 (accept_3_2 67 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 185 5 13 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 185 (accept_3_2 64 75 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 185 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 75
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 185 (accept_3_2 61 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75
  185 5 12 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  75 185 (Polychromatic418967fa.accept_13_7_10_3_1_1505 59 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 185 (accept_3_2 58 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 185 5 11 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 185 (accept_3_2 52 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 185 5 10 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 185 (accept_3_2 49 75 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 185 (Polychromatic418967fa.accept_19_10_18_14_1_7867 48 75
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 185 (accept_3_2 46 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  185 5 9 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 185 (accept_3_2 43 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 185 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 75
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 185 5 8 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 185
  (Polychromatic418967fa.accept_17_5_7_15_1_1230 39 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 185 (accept_3_2 37 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 185 5 7 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 185 (accept_3_2 34 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 185 (accept_3_2 31 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  185 5 6 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 185 (accept_3_2 28 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 185 (Polychromatic418967fa.accept_20_7_15_5_1_6087 27 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 185 5 5 15 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 185
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 185 (accept_3_2 22 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 185 5 4 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 185 (accept_3_2 19 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 185 (accept_3_2 16 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  185 5 3 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 185 (accept_3_2 13 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 185 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 75 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 185 5 2 15 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 185 (accept_3_2 7 75 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 185 5 1 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 185 (accept_3_2 4 75 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 185 (Polychromatic418967fa.accept_19_3_18_14_1_5020 3 75 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 185 (accept_3_2 1 75 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 185 (allA_succ_of_accept
  73 74 185 (accept_3_2 73 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 185
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 185 (accept_3_2 70 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 185 (Polychromatic418967fa.accept_12_8_2_5_1_844
  68 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 185 (accept_3_2 67
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 185
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 185 (accept_3_2 64 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 62
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 185 (accept_3_2 61 74
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 185
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 185 (accept_3_2 58 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 185 (Polychromatic418967fa.accept_10_6_4_5_1_615
  56 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 185 (accept_3_2 55
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 185
  (Polychromatic418967fa.accept_11_10_8_9_1_492 54 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 185 (accept_3_2 52 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 185 (accept_3_2 49 74
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 185 (accept_3_2 46 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 44
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 185 (accept_3_2 43 74
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 185
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 185 (accept_3_2 40 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 185 (Polychromatic418967fa.accept_13_12_9_3_1_3047
  38 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 37 74 185 37 1 2 5 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 36 74 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 185 (accept_3_2 34 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 185 (Polychromatic418967fa.accept_11_10_8_9_1_492
  32 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 185 (accept_3_2 31
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 185
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 185 (accept_3_2 28 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 26
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 185 (accept_3_2 25 74
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 185
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 185 (accept_3_2 22 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 185 (accept_3_2 19 74
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 185
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 185 (accept_3_2 16 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 185
  (Polychromatic418967fa.accept_17_14_6_15_1_3151 14 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 185 (accept_3_2 13 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 185 (accept_3_2 10 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 185 (accept_3_2 7 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 185 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 185 (accept_3_2 4 74 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 185 (Polychromatic418967fa.accept_13_2_9_3_1_2212 2
  74 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 185 (accept_3_2 1 74 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 185 (allA_of_3_0 73 73 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 185 (allA_succ_of_accept 71 72 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 185 (accept_3_2 70 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 185 (accept_3_2 67 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 185 (Polychromatic418967fa.accept_13_1_7_3_1_1503 66 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 185
  (Polychromatic418967fa.accept_16_1_8_9_1_3462 65 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 185 (accept_3_2 64 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 185 (accept_3_2 61 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 185 (Polychromatic418967fa.accept_13_8_7_3_1_430 60 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 185
  (Polychromatic418967fa.accept_22_15_6_9_1_10627 59 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 185 (accept_3_2 58 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 185 (Polychromatic418967fa.accept_13_4_7_3_1_92 56 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 185 (accept_3_2 55 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 185
  (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 185 (accept_3_2 52 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 185 (accept_3_2 49 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 185 (accept_3_2 46 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 185 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 185 (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 185 (accept_3_2 43 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 185 (Polychromatic418967fa.accept_19_4_15_14_1_10614 42 72
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 185 (accept_3_2 40 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 185 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 185 (accept_3_2 37 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 185
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 185 (accept_3_2 34 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 185 (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 185 (accept_3_2 31 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 185 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 72 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 185 (accept_3_2 28 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 185 (accept_3_2 25 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 185 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 185
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 185 (accept_3_2 22 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 185 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 185 (accept_3_2 19 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 185
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 185 (accept_3_2 16 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 185 (accept_3_2 13 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 185
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 185 (accept_3_2 10 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 185 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 185 (accept_3_2 7 72 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 185 (accept_3_2 4 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  185 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 72 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 185 (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 72 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 185 (accept_3_2 1 72 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 185
  (allA_succ_of_accept 70 71 185 (accept_3_2 70 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 185 (accept_3_2 67 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 185 (accept_3_2 64 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 185 (Polychromatic418967fa.accept_17_12_3_15_1_5476 63 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 185 (accept_3_2 61 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 185 (accept_3_2 58 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 185 (accept_3_2 55 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 185 (accept_3_2 52 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 185 (accept_3_2 49 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 185 (accept_3_2 46 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 185 (Polychromatic418967fa.accept_16_13_7_9_1_2606 45 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 185 (accept_3_2 43 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 185
  (Polychromatic418967fa.accept_21_20_8_17_1_7437 41 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 185 (accept_3_2 40 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 185 (accept_3_2 37 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 185
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 185 (accept_3_2 34 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 185 (accept_3_2 31 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 185 (accept_3_2 28 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 185 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 185 (accept_3_2 25 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 185 (accept_3_2 22 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 185 (accept_3_2 19 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 185 (accept_3_2 16 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 185 (accept_3_2 13 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 185 (accept_3_2 10 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 185 (accept_3_2 7 71 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 185 (accept_3_2 4 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 71 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 185 (accept_3_2 1 71 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 185
  (allA_of_3_0 70 70 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 185 (allA_succ_of_accept 68 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 185 (accept_3_2 67 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 185 (accept_3_2 64 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 185 (accept_3_2 61 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 185 (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 185 (accept_3_2 58 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 185 (accept_3_2 55 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 185 (accept_3_2 52 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 185 (accept_3_2 49 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 185 (accept_3_2 46 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 185 (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 185 (accept_3_2 43 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 185 (accept_3_2 40 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 185 (accept_3_2 37 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 185 (accept_3_2 34 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 185 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 185 (accept_3_2 31 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 185 (accept_3_2 28 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 185 (accept_3_2 25 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 185 (accept_3_2 22 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 185 (accept_3_2 19 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 185 (accept_3_2 16 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 185 (accept_3_2 13 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 185 (accept_3_2 10 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 185 (accept_3_2 7 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 185 (Polychromatic418967fa.accept_22_5_3_9_1_9062 5 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 185 (accept_3_2 4 69 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 185 (accept_3_2 1 69 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 185 (allA_succ_of_accept 67 68
  185 (accept_3_2 67 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 185
  (Polychromatic418967fa.accept_19_9_11_14_1_10626 66 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 185 (accept_3_2 64 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 185 (accept_3_2 61 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 185 (Polychromatic418967fa.accept_16_12_4_9_1_4633 60 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 185 (accept_3_2 58 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 185
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 185 (accept_3_2 55 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 185 (Polychromatic418967fa.accept_19_16_11_14_1_3608 54 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 185 (accept_3_2 52 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 185 (accept_3_2 49 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 185 (accept_3_2 46 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 185 (accept_3_2 43 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 185 (accept_3_2 40 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 185 (accept_3_2 37 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 185 (Polychromatic418967fa.accept_19_16_11_14_1_3608 35 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 185 (accept_3_2 34 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 185 (accept_3_2 31 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 185 (accept_3_2 28 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 185
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 185 (accept_3_2 25 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 185 (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 185 (accept_3_2 22 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 185
  (Polychromatic418967fa.accept_26_20_16_3_1_10625 20 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 68 185 (accept_3_2 19 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 68 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 68 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 68 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 185 (accept_3_2 16 68 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 185 (accept_3_2 13 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 185 (accept_3_2 10 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 185 (accept_3_2 7 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  185 (Polychromatic418967fa.accept_19_6_11_14_1_10624 6 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 68 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 185 (accept_3_2 4 68 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 185 (accept_3_2 1 68 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 185 (allA_of_3_0 67 67 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 185 (allA_succ_of_accept 65 66 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 185 (accept_3_2 64 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 185 (accept_3_2 61 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 185 (accept_3_2 58 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 185 (Polychromatic418967fa.accept_13_5_1_3_1_878 57 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 185 (accept_3_2 55 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 185 (accept_3_2 52 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 185 (Polychromatic418967fa.accept_13_11_1_3_1_910 50 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 185 (accept_3_2 49 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 185 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 185 (accept_3_2 46 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 185 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 185 (accept_3_2 43 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 185
  (Polychromatic418967fa.accept_10_1_6_5_1_304 41 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 185 (accept_3_2 40 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 185 (accept_3_2 37 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 185 (Polychromatic418967fa.accept_19_17_9_14_1_10623 36 66 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 185 (accept_3_2 34 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 185 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 185 (accept_3_2 31 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 185 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 185 (accept_3_2 28 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 185 (accept_3_2 25 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 185 (accept_3_2 22 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 185 (accept_3_2 19 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 185 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 185 (accept_3_2 16 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 185 (accept_3_2 13 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 185 (accept_3_2 10 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 185 (accept_3_2 7 66 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 66 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 185
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 185 (accept_3_2 4 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 66 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 185 (accept_3_2 1 66 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 185
  (allA_succ_of_accept 64 65 185 (accept_3_2 64 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 185 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 185 (accept_3_2 61 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 185 5 12 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 185 (Polychromatic418967fa.accept_19_2_8_14_1_3648 59 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 185 (accept_3_2 58 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 57
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 185
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 185 5 11 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 185 (accept_3_2 52 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 185 5 10 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 185 (accept_3_2 49
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 185 (accept_3_2 46 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 185 5 9 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 185 (accept_3_2 43 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 185 5 8 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 185 (Polychromatic418967fa.accept_23_15_19_1_1_10622 38 65
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 185 (accept_3_2 37 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 185 5 7 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 185 (accept_3_2 34
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 185 (Polychromatic418967fa.accept_18_14_11_5_1_7967 32 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 185 (accept_3_2 31 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 185 5 6 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 185 (accept_3_2 28 65 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 185 5 5 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 185 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 185 (accept_3_2 22 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 185 5 4 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 185 (accept_3_2 19
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 185
  (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 185 (accept_3_2 16 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 185 5 3 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 185 (Polychromatic418967fa.accept_18_14_11_5_1_7967 14 65 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 185 (accept_3_2 13 65 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 185
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 185 5 2 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 185 (Polychromatic418967fa.accept_19_9_8_14_1_10621 9 65 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 185 (accept_3_2 7 65 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 185 5 1 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 185 (accept_3_2 4 65
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 185 (Polychromatic418967fa.accept_9_3_2_5_1_234
  3 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 185
  (Polychromatic418967fa.accept_16_2_1_9_1_2577 2 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 185 (accept_3_2 1 65 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 185 (allA_of_3_0 64 64 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 185 (allA_succ_of_accept 62 63 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 185 (accept_3_2 61 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 185 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 185 (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 185 (accept_3_2 58 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 185 (accept_3_2 55 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 185 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 185 (accept_3_2 52 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 51 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 185 (accept_3_2 49 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 185 (accept_3_2 46 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 185 (accept_3_2 43 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 185 (Polychromatic418967fa.accept_13_2_11_3_1_873 41 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 185 (accept_3_2 40 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 185 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 185 (accept_3_2 37 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 185 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 185 (Polychromatic418967fa.accept_17_1_12_15_1_1263 35 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 185 (accept_3_2 34 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 185 (accept_3_2 31 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 185 (Polychromatic418967fa.accept_19_10_6_14_1_4959 29 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 185 (accept_3_2 28 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 185 (accept_3_2 25 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 185 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 185 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 185 (accept_3_2 22 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 185 (accept_3_2 19 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 185 (accept_3_2 16 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 185 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 185 (accept_3_2 13 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 185 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 185 (accept_3_2 10 63 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 185 (accept_3_2 7 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 185 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 63 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 185 (accept_3_2 4 63 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 185 (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 63 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 185 (accept_3_2 1 63 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 185 (allA_succ_of_accept 61 62 185
  (accept_3_2 61 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 185 (accept_3_2 58 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 185 (accept_3_2 55 62
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 185
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 185 (accept_3_2 52 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 185
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 50 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 185 (accept_3_2 49 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 185 (accept_3_2 46 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 185 (accept_3_2 43 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 185 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 185 (accept_3_2 40 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 185 (accept_3_2 37 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 185 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 185 (accept_3_2 34 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 185 (accept_3_2 31 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 185 (accept_3_2 28 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 185
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 185 (accept_3_2 25 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 185 (accept_3_2 22 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 185 (accept_3_2 19 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 185 (accept_3_2 16 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 185
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 185 (accept_3_2 13 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 185 (accept_3_2 10 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 185 (accept_3_2 7 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 185 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 185 (accept_3_2 4 62 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  62 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 185 (accept_3_2 1 62 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 185 (allA_of_3_0 61 61 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 185 (allA_succ_of_accept 59 60 185
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 185 (accept_3_2 58 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 185 5 11 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 185
  (Polychromatic418967fa.accept_19_16_3_14_1_9212 54 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 185 (accept_3_2 52 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 185 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 185 5 10 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 185 (accept_3_2 49 60 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 60 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 185 (accept_3_2 46 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60
  185 5 9 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  60 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 60 185 (accept_3_2 43 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 60 185 (Polychromatic418967fa.accept_24_18_12_17_1_10620 42 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 185 5 8 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 185 (accept_3_2 37 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 185 5 7 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 185 (accept_3_2 34 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 185 (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 60 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 185
  (Polychromatic418967fa.accept_23_9_14_1_1_8977 32 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 185 (accept_3_2 31 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  185 5 6 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 185 (accept_3_2 28 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 60 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 60 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 185 5 5 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 185
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 185 (Polychromatic418967fa.accept_17_6_9_15_1_3185 23 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 185 (accept_3_2 22 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 185 5 4 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 185 (accept_3_2 19 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 185 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 185 (accept_3_2 16 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60
  185 5 3 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  60 185 (Polychromatic418967fa.accept_21_14_18_17_1_10619 14 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 185 (accept_3_2 13 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 185 5 2 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 185
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 185 (accept_3_2 7 60 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 60 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 185 5 1 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 185 (accept_3_2 4 60 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 185 (accept_3_2 1 60 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 185 (allA_succ_of_accept 58 59 185
  (accept_3_2 58 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 185
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 185 (accept_3_2 55 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 185 (Polychromatic418967fa.accept_13_1_7_3_1_1503
  53 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 185 (accept_3_2 52
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 185 (accept_3_2 49 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 185 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 185 (Polychromatic418967fa.accept_13_8_7_3_1_430
  47 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 185 (accept_3_2 46
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 185
  (Polychromatic418967fa.accept_19_7_2_14_1_3569 45 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 44 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 185 (accept_3_2 43 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 185 (accept_3_2 40 59
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 185
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 39 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 185 (accept_3_2 37 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 185 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 185 (Polychromatic418967fa.accept_11_2_4_9_1_484
  35 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 185 (accept_3_2 34
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 185
  (Polychromatic418967fa.accept_20_13_19_5_1_1012 33 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 185 (accept_3_2 31 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 185 (Polychromatic418967fa.accept_22_7_15_9_1_5710
  29 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 185 (accept_3_2 28
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 185
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 185 (accept_3_2 25 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 185 (Polychromatic418967fa.accept_13_10_7_3_1_3041
  23 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 185 (accept_3_2 22
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 185 (Polychromatic418967fa.accept_16_4_11_9_1_1631 20 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 185 (accept_3_2 19 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 185 (Polychromatic418967fa.accept_13_4_7_3_1_92 17
  59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 185 (accept_3_2 16 59
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 185
  (Polychromatic418967fa.accept_20_15_19_5_1_7718 15 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 185 (accept_3_2 13 59 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 59 185 (Polychromatic418967fa.accept_19_12_2_14_1_10618 12 59 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 185
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 185 (accept_3_2 10 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 185 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 185 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 185 (accept_3_2 7 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 185
  (Polychromatic418967fa.accept_16_5_11_9_1_861 5 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 185 (accept_3_2 4 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  185 (Polychromatic418967fa.accept_22_3_15_9_1_10617 3 59 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 185 (accept_3_2 1 59 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 185
  (allA_of_3_0 58 58 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 185 (allA_succ_of_accept 56 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 185 (accept_3_2 55 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 185 (accept_3_2 52 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 185 (accept_3_2 49 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 185 (accept_3_2 46 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 185 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 185 (accept_3_2 43 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 185 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 185 (accept_3_2 40 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 185 (accept_3_2 37 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 185 (accept_3_2 34 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 185 (accept_3_2 31 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 185 (accept_3_2 28 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 185 (accept_3_2 25 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 185 (accept_3_2 22 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 185 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 185 (accept_3_2 19 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 185 (accept_3_2 16 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 185 (accept_3_2 13 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 185 (accept_3_2 10 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 185 (accept_3_2 7 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 185 (accept_3_2 4 57 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 57 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 185 (accept_3_2 1 57 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 185)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 185 (allA_succ_of_accept 55 56 185 (accept_3_2 55 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 185 (accept_3_2 52 56 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 185 (accept_3_2 49 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 185 (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 185 (accept_3_2 46 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 185 (accept_3_2 43 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 185 (accept_3_2 40 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 185 (accept_3_2 37 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 185 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 185 (accept_3_2 34 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 185
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 185 (accept_3_2 31 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 185 (accept_3_2 28 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 185 (accept_3_2 25 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 185 (accept_3_2 22 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 185
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 185 (accept_3_2 19 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 185 (Polychromatic418967fa.accept_20_18_16_5_1_9137 18 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 185 (accept_3_2 16 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 185 (accept_3_2 13 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 185 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 185 (accept_3_2 10 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 185 (accept_3_2 7 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 185 (Polychromatic418967fa.accept_21_5_14_17_1_10616 5 56 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 185 (accept_3_2 4 56 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 185 (accept_3_2 1 56 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 185))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 185 (allA_of_3_0 55 55 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 185
  (allA_succ_of_accept 53 54 185 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 185 (accept_3_2 52 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 185 (accept_3_2 49 54
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 185
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 185 (accept_3_2 46 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 185 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 185 (accept_3_2 43 54
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 185
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 185 (accept_3_2 40 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 185 (Polychromatic418967fa.accept_13_12_2_3_1_1527
  38 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 185 (accept_3_2 37
  54 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 185 (accept_3_2 34 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 185 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 54 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 185
  (Polychromatic418967fa.accept_19_13_16_14_1_3517 32 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 54 185 (accept_3_2 31 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 54 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 185 (accept_3_2 28 54 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 185
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 185 (accept_3_2 25 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 185 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 185 (accept_3_2 22 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 185
  (Polychromatic418967fa.accept_25_20_4_10_1_10615 20 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 54 185 (accept_3_2 19 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 54 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 185 (Polychromatic418967fa.accept_19_17_16_14_1_10604 17 54
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 185 (accept_3_2 16 54 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 185
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 185 (accept_3_2 13 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 185 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 185 (accept_3_2 10 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 185 (accept_3_2 7 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  185 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 185 (accept_3_2 4 54 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 185 (accept_3_2 1 54 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 185))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 185 (allA_succ_of_accept 52 53 185 (accept_3_2 52 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 53 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 185 (accept_3_2 49 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 48
  53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 185 (accept_3_2 46 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 185 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 185 (accept_3_2 43 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 185 (accept_3_2 40 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 185 (accept_3_2 37 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 185
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 185 (accept_3_2 34 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 185 (accept_3_2 31 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 185 (accept_3_2 28 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 185 (accept_3_2 25 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 185
  (Polychromatic418967fa.accept_19_4_15_14_1_10614 23 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 53 185 (accept_3_2 22 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 53 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 185 (accept_3_2 19 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 185 (Polychromatic418967fa.accept_10_8_3_5_1_613
  18 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 185 (accept_3_2 16 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 185 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 185 (accept_3_2 13 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 185 (accept_3_2 10 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 185 (Polychromatic418967fa.accept_24_9_5_17_1_10613 9 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 185 (accept_3_2 7 53 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 185
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 185 (accept_3_2 4 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 185 (accept_3_2 1 53 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 185))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 185 (allA_of_3_0 52 52
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 185 (allA_succ_of_accept 50 51 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 185 (accept_3_2 49 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 185 (accept_3_2 46 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 185 (accept_3_2 43 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 185 (accept_3_2 40 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 185 (accept_3_2 37 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 185 (accept_3_2 34 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 185 (accept_3_2 31 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 185 (accept_3_2 28 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 185 (accept_3_2 25 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 185 (Polychromatic418967fa.accept_16_7_3_9_1_2557 23 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 185 (accept_3_2 22 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 185 (accept_3_2 19 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 185 (accept_3_2 16 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 185 (accept_3_2 13 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 185 (accept_3_2 10 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 185 (accept_3_2 7 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 185 (accept_3_2 4 51 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 185 (accept_3_2 1 51 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 185)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 185 (allA_succ_of_accept 49 50 185 (accept_3_2 49 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 185 (Polychromatic418967fa.accept_17_14_16_15_1_5509 48 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 185 (accept_3_2 46 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 185 5 9 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 50 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 185 (accept_3_2 43 50
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 185
  (Polychromatic418967fa.accept_20_2_10_5_1_6082 42 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 185 (Polychromatic418967fa.accept_13_2_11_3_1_873 41 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 185 5 8 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 185
  (Polychromatic418967fa.accept_16_6_2_9_1_5897 38 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 185 (accept_3_2 37 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 185 5 7 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 185 (accept_3_2 34 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 185 (accept_3_2 31 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 185 5 6 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 185 (Polychromatic418967fa.accept_18_11_14_5_1_3951
  29 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 185 (accept_3_2 28
  50 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 50 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 50 185 5 5 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 50 185 (Polychromatic418967fa.accept_20_4_10_5_1_3305 24 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 50 185 (accept_3_2 22 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  50 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 50 185 5 4 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 185 (accept_3_2 19 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 50 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 50 185 (Polychromatic418967fa.accept_16_1_2_9_1_1607 17 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 185 (accept_3_2 16 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 50 185 5 3 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 50 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 185 (accept_3_2 13
  50 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 185 5 2 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 185 (accept_3_2 7 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  185 (Polychromatic418967fa.accept_16_6_2_9_1_5897 6 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 50 185 5 1 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 50 185 (accept_3_2 4 50 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 50 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 185 (accept_3_2 1 50 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 185)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 185 (allA_of_3_0 49 49 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 185 (allA_succ_of_accept 47 48
  185 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 185 (accept_3_2 46 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 185 (accept_3_2 43 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 185
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 185 (accept_3_2 40 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 185 (accept_3_2 37 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 185 (accept_3_2 34 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 185 (accept_3_2 31 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 185 (accept_3_2 28 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 185 (accept_3_2 25 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 185 (accept_3_2 22 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 185 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 185 (accept_3_2 19 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 185 (accept_3_2 16 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 185 (Polychromatic418967fa.accept_20_14_8_5_1_6090 14 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 185 (accept_3_2 13 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 185 (accept_3_2 10 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 185 (accept_3_2 7 48 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 185
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 185 (accept_3_2 4 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  185 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 185 (accept_3_2 1 48 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 185)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 185 (allA_succ_of_accept 46
  47 185 (accept_3_2 46 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 185
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 45 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 185 (accept_3_2 43 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 185
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 185 (accept_3_2 40 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 185 (accept_3_2 37 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 185 (accept_3_2 34 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 185 (accept_3_2 31 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 185 (accept_3_2 28 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 185 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 185 (accept_3_2 25 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 185 (accept_3_2 22 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 185 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 185 (accept_3_2 19 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 185 (accept_3_2 16 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 185 (accept_3_2 13 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 185
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 185 (accept_3_2 10 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 185 (accept_3_2 7 47 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 185
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 185 (accept_3_2 4 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 185 (accept_3_2 1 47 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 185))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 185 (allA_of_3_0 46 46 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 185 (allA_succ_of_accept 44 45 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 185 (accept_3_2 43 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 185 (Polychromatic418967fa.accept_19_4_7_14_1_3537 42 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 185 (Polychromatic418967fa.accept_19_3_7_14_1_3669 41 45 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 185 5 8 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 185
  (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 185 (accept_3_2 37 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 185 5 7 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 185 (accept_3_2 34 45 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 185 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 45 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 185 (accept_3_2 31 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45
  185 5 6 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  45 185 (Polychromatic418967fa.accept_19_10_7_14_1_3592 29 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 185 (accept_3_2 28 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 185 5 5 9 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 185
  (Polychromatic418967fa.accept_22_2_1_9_1_10612 24 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 185 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 185 (accept_3_2 22 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 185 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 185 5 4 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 185 (accept_3_2 19 45 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 185 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 45 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 185
  (Polychromatic418967fa.accept_16_1_13_9_1_2551 17 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 185 (accept_3_2 16 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45
  185 5 3 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  45 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 185 (accept_3_2 13 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 185 (Polychromatic418967fa.accept_19_11_7_14_1_6394 11 45
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 185 5 2 9 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 185
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 185 (accept_3_2 7 45 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 185 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 45 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 185 5 1 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 185 (accept_3_2 4 45 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 185 (accept_3_2 1 45 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  185))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 185 (allA_succ_of_accept 43 44 185 (accept_3_2 43 44
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 185 (accept_3_2 40 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 38
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 185 (accept_3_2 37 44
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 185 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 185 (accept_3_2 34 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 185 (Polychromatic418967fa.accept_13_6_5_3_1_426
  32 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 185 (accept_3_2 31
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 185
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 185 (accept_3_2 28 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 185 (accept_3_2 25 44
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 185 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 185 (accept_3_2 22 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 185 (accept_3_2 19 44
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 185
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 185 (accept_3_2 16 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 185 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 185 (accept_3_2 13
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 185 (accept_3_2 10 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 185 (accept_3_2 7 44 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 185 (accept_3_2 4 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 185 (accept_3_2 1 44 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 185)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 185 (allA_of_3_0 43 43 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 185 (allA_succ_of_accept 41 42 185
  (Polychromatic418967fa.accept_23_18_19_1_1_10611 41 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 42 185 (accept_3_2 40 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 42 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 185 (accept_3_2 37 42 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108
  36 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 185 (accept_3_2 34 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 185 (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 185 (accept_3_2 31 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 185 (accept_3_2 28 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 185 (accept_3_2 25 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 185 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 185 (accept_3_2 22 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 185 (accept_3_2 19 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 185 (accept_3_2 16 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 185 (Polychromatic418967fa.accept_22_14_20_9_1_10610 14 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 185 (accept_3_2 13 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 185 (accept_3_2 10 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 185 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 185 (accept_3_2 7 42 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 42 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 185
  (Polychromatic418967fa.accept_23_5_19_1_1_10609 5 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 185 (accept_3_2 4 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 185 (accept_3_2 1 42 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 185)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 185 (allA_succ_of_accept 40 41
  185 (accept_3_2 40 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 185 (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 41 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 185 (accept_3_2 37 41 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 185 (Polychromatic418967fa.accept_13_9_2_3_1_3027
  35 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 185 (accept_3_2 34
  41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 185
  (Polychromatic418967fa.accept_22_11_19_9_1_10608 33 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 185 (accept_3_2 31 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 185 (accept_3_2 28 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 185 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 185 (accept_3_2 25 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 185 (accept_3_2 22 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 185 (Polychromatic418967fa.accept_25_20_16_10_1_10607 20 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 185 (accept_3_2 19 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 185 (accept_3_2 16 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 185 (Polychromatic418967fa.accept_20_15_1_5_1_6049 15 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 185 (accept_3_2 13 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 185 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 185 (accept_3_2 10 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 185 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 185 (accept_3_2 7 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 41 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 185
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 185 (accept_3_2 4 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  185 (Polychromatic418967fa.accept_20_3_1_5_1_4643 3 41 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 185 (accept_3_2 1 41 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 185))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 185 (allA_of_3_0 40 40
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 185 (allA_succ_of_accept 38 39 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 185 (accept_3_2 37 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 185 (accept_3_2 34 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 185 (accept_3_2 31 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 185 (accept_3_2 28 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 185 (accept_3_2 25 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 185 (Polychromatic418967fa.accept_25_23_14_10_1_6861 23 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 185 (accept_3_2 22 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 185 (accept_3_2 19 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 185 (accept_3_2 16 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 185 (accept_3_2 13 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 185 (accept_3_2 10 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 185 (accept_3_2 7 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 185 (Polychromatic418967fa.accept_31_5_8_30_1_10606 5 39 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 185 (accept_3_2 4 39 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 39 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 185 (accept_3_2 1 39 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 185))))))))))))))))))))))))))))))))))))))) (allB_succ 38 185
  (allA_succ_of_accept 37 38 185 (accept_3_2 37 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 185 (Polychromatic418967fa.accept_17_2_4_15_1_5451 36 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 185 (accept_3_2 34 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 185 (accept_3_2 31 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 185 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 185 (accept_3_2 28 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 185 (accept_3_2 25 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 185 (accept_3_2 22 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 185
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 185 (accept_3_2 19 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 185 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 185 (accept_3_2 16 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 185
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 185 (accept_3_2 13 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 185 (accept_3_2 10 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 185 (accept_3_2 7 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 185 (Polychromatic418967fa.accept_22_5_16_9_1_10605 5 38 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 185 (accept_3_2 4 38 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  38 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 185 (accept_3_2 1 38 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 185)))))))))))))))))))))))))))))))))))))) (allB_succ 37 185
  (allA_of_3_0 37 37 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 185 (allA_succ_of_accept 35 36 185
  (Polychromatic418967fa.accept_19_16_17_14_1_4969 35 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 36 185 (accept_3_2 34 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 36 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 185 (accept_3_2 31 36 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30
  36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 185 (accept_3_2 28 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 185 (accept_3_2 25 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 185 (accept_3_2 22 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 185 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 36 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 185 (accept_3_2 19 36 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 185
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 185 (accept_3_2 16 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 185 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 185 (accept_3_2 13 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 185 (accept_3_2 10 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 185 (Polychromatic418967fa.accept_16_8_4_9_1_4666 8 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 185 (accept_3_2 7 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 36 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 185 (accept_3_2 4 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 36 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 185 (accept_3_2 1 36 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 185)))))))))))))))))))))))))))))))))))) (allB_succ 35 185 (allA_succ_of_accept 34 35
  185 (accept_3_2 34 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 35 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 185 (accept_3_2 31 35 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 185 5 6 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 185 (accept_3_2 28 35 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 185 (Polychromatic418967fa.accept_20_7_15_5_1_6087 27 35 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 185 5 5 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 185 (Polychromatic418967fa.accept_16_7_3_9_1_2557 23 35 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 185 (accept_3_2 22 35 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 185 5 4 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 185 (accept_3_2 19
  35 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 185 (Polychromatic418967fa.accept_19_17_16_14_1_10604 17 35 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 185 (accept_3_2 16 35 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 185 5 3 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 35 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 185 (accept_3_2 13 35 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 185 5 2 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 185 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 35 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 185 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 35 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 185 (accept_3_2 7 35 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 185 5 1 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 185 (accept_3_2 4 35
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 185 (Polychromatic418967fa.accept_9_3_8_5_1_65
  3 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 185 (accept_3_2 1 35 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  185))))))))))))))))))))))))))))))))))) (allB_succ 34 185 (allA_of_3_0 34 34 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 185 (allA_succ_of_accept 32 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 185 (accept_3_2 31 33 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 185 (accept_3_2 28 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 185 (accept_3_2 25 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 185 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 185 (accept_3_2 22 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 185 (accept_3_2 19 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 33 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 185 (accept_3_2 16 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 185 (accept_3_2 13 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 185 (accept_3_2 10 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 185 (accept_3_2 7 33 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 33 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 185
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 185 (accept_3_2 4 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 185 (accept_3_2 1 33 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 185))))))))))))))))))))))))))))))))) (allB_succ 32 185 (allA_succ_of_accept 31 32 185
  (accept_3_2 31 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 185
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 185 (accept_3_2 28 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 185 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 185 (accept_3_2 25
  32 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 185
  (Polychromatic418967fa.accept_19_5_13_14_1_6366 24 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 185 (accept_3_2 22 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 185 (accept_3_2 19 32
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 185 (accept_3_2 16 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 185 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 185 (accept_3_2 13
  32 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 185
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 185 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 185 (accept_3_2 10 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 185 (accept_3_2 7 32 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 185
  (Polychromatic418967fa.accept_13_5_6_3_1_868 5 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 185 (accept_3_2 4 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 185 (accept_3_2 1 32 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 185)))))))))))))))))))))))))))))))) (allB_succ 31 185 (allA_of_3_0 31 31 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 185 (allA_succ_of_accept 29 30 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 185 (accept_3_2 28 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 185 5 5 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24
  30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 185 (accept_3_2 22 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 30 185 5 4 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 185 (accept_3_2 19 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 30 185 (Polychromatic418967fa.accept_20_18_10_5_1_3306 18 30 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 185 (accept_3_2 16 30 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 185 5 3 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 185 (Polychromatic418967fa.accept_13_1_4_3_1_1545
  14 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 185 (accept_3_2 13
  30 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 185 5 2 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 185 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 30 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 185 (accept_3_2 7 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30
  185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 185 5 1 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 185 (accept_3_2 4 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 185 (accept_3_2 1 30 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 185)))))))))))))))))))))))))))))) (allB_succ 29 185 (allA_succ_of_accept 28 29 185
  (accept_3_2 28 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 185
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 185 (accept_3_2 25 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 23
  29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 185 (accept_3_2 22 29
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 185
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 185 (accept_3_2 19 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 185 (accept_3_2 16 29
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 185
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 185 (accept_3_2 13 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 185 (accept_3_2 10 29
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 185 (Polychromatic418967fa.accept_7_2_1_3_1_102
  9 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 185 (accept_3_2 7 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 185 (accept_3_2 4 29 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 29 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  29 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 185 (accept_3_2 1 29 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 185))))))))))))))))))))))))))))) (allB_succ 28 185 (allA_of_3_0
  28 28 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 185 (allA_succ_of_accept 26 27 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 185 (accept_3_2 25 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 185 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 185 (accept_3_2 22 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 185 (accept_3_2 19 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 185 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 185 (accept_3_2 16 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 185 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 27 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 185 (accept_3_2 13 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 185 (accept_3_2 10 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 185 (accept_3_2 7 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 185 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 27 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 185 (accept_3_2 4 27 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 185 (accept_3_2 1 27 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 185))))))))))))))))))))))))))) (allB_succ 26 185
  (allA_succ_of_accept 25 26 185 (accept_3_2 25 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 185 (accept_3_2 22 26 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 185 (accept_3_2 19 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 185 (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 185 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 26 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 185 (accept_3_2 16 26 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 185
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 185 (accept_3_2 13 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 185 (accept_3_2 10 26 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 185 (accept_3_2 7 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 26 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 185 (Polychromatic418967fa.accept_14_5_12_3_1_3397 5 26 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 185 (accept_3_2 4 26 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 185 (accept_3_2 1 26 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 185)))))))))))))))))))))))))) (allB_succ 25 185 (allA_of_3_0 25
  25 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 185 (allA_succ_of_accept 23 24 185
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 185 (accept_3_2 22 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 185 (accept_3_2 19 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 24 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 185 (accept_3_2 16 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 185 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 185 (Polychromatic418967fa.accept_13_1_11_3_1_901 14 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 185 (accept_3_2 13 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 24 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 185 (accept_3_2 10 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 185 (accept_3_2 7 24 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 185
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 185 (accept_3_2 4 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 24 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 185 (accept_3_2 1 24 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 185)))))))))))))))))))))))) (allB_succ 23 185 (allA_succ_of_accept 22 23 185 (accept_3_2 22
  23 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 185
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 185 (accept_3_2 19 23 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 185 (Polychromatic418967fa.accept_10_7_3_5_1_301
  17 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 185 (accept_3_2 16
  23 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 185 (accept_3_2 13 23 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 185
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 185 (accept_3_2 10 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 185 (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 185 (accept_3_2 7 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 185 (accept_3_2 4 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  185 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 23 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 185 (accept_3_2 1 23 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 185))))))))))))))))))))))) (allB_succ 22 185 (allA_of_3_0 22 22 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 21 185 (allA_succ_of_accept 20 21 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 185 (accept_3_2 19 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 185 (accept_3_2 16 21 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 185 (accept_3_2 13 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 185 (accept_3_2 10 21 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 185 (accept_3_2 7 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 21 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 185 (accept_3_2 4 21 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 185 (accept_3_2 1 21 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 185))))))))))))))))))))) (allB_succ 20 185 (allA_succ_of_accept
  19 20 185 (accept_3_2 19 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 185 (accept_3_2 16 20 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 185 5 3 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 20 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 185 (accept_3_2 13 20 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 185 5 2 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 20 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 185 (accept_3_2 7 20 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 185 5 1 4 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 185 (accept_3_2 4 20
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 185 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 185 (accept_3_2 1 20 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  185)))))))))))))))))))) (allB_succ 19 185 (allA_of_3_0 19 19 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 185 (allA_succ_of_accept 17 18 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 18 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 185 (accept_3_2 16 18 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 185
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 185 (accept_3_2 13 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 185 (accept_3_2 10 18 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 185 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 18 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 185 (accept_3_2 7 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 185 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 18 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 185 (accept_3_2 4 18 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  18 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 185 (accept_3_2 1 18 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 185)))))))))))))))))) (allB_succ 17 185 (allA_succ_of_accept 16
  17 185 (accept_3_2 16 17 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 17 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 17 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 185 (accept_3_2 13 17 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 185 (accept_3_2 10 17
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 185
  (Polychromatic418967fa.accept_19_9_17_14_1_6357 9 17 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 17 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 185 (accept_3_2 7 17 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 185 (Polychromatic418967fa.accept_16_5_1_9_1_4621 5
  17 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 185 (accept_3_2 4 17 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 17 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 185 (accept_3_2 1 17 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  185))))))))))))))))) (allB_succ 16 185 (allA_of_3_0 16 16 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  185 (allA_succ_of_accept 14 15 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 185 (accept_3_2 13 15 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  15 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 185 5 2 3 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 185 (accept_3_2 7 15 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 185 5 1 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 185 (accept_3_2 4 15 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 185 (accept_3_2 1 15 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  185))))))))))))))) (allB_succ 14 185 (allA_succ_of_accept 13 14 185 (accept_3_2 13 14 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 185 (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 14 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 185 (accept_3_2 10 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 185 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 14 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 185 (accept_3_2 7 14 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 185
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 185 (accept_3_2 4 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 185 (Polychromatic418967fa.accept_13_2_1_3_1_419 2 14 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 185 (accept_3_2 1 14 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 185)))))))))))))) (allB_succ 13 185 (allA_of_3_0 13 13 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 185 (allA_succ_of_accept 11 12 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 185 (accept_3_2 10 12 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 185 (accept_3_2 7 12 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 12 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 185 (accept_3_2 4 12 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 185 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 185 (accept_3_2 1 12 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 185)))))))))))) (allB_succ 11 185 (allA_succ_of_accept 10 11 185
  (accept_3_2 10 11 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 185
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 185 (accept_3_2 7 11 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 185 (Polychromatic418967fa.accept_13_5_11_3_1_902 5
  11 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 185 (accept_3_2 4 11 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  11 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 185 (accept_3_2 1 11 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  185))))))))))) (allB_succ 10 185 (allA_of_3_0 10 10 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 185
  (allA_succ_of_accept 8 9 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 185 (accept_3_2 7 9 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 185 (accept_3_2 4 9 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 185 (accept_3_2 1 9 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 185)))))))))
  (allB_succ 8 185 (allA_succ_of_accept 7 8 185 (accept_3_2 7 8 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 8 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 185 (accept_3_2 4 8 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 185 (accept_3_2 1 8 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 185))))))))
  (allB_succ 7 185 (allA_of_3_0 7 7 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 185 (allA_succ_of_accept 5
  6 185 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 6 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 6 185 (accept_3_2 4 6 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 185 (accept_3_2 1 6 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 185)))))) (allB_succ 5 185 (allA_succ_of_accept 4 5 185 (accept_3_2 4 5
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 185
  (Polychromatic418967fa.accept_19_3_5_14_1_3584 3 5 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 185 (accept_3_2 1 5 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 185))))) (allB_succ 4 185 (allA_of_3_0 4 4 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 185 (allA_succ_of_accept 2 3 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 185 (accept_3_2 1 3 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 185))) (allB_succ 2 185 (allA_succ_of_accept 1 2 185 (accept_3_2 1 2 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 185)) (allB_two
  185))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


