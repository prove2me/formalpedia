-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch191_Segment000
-- name    : Polychromatic418967fa_Branch191_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:30:10.839202+00:00
-- url     : https://prove2.me/theorems/c36b8156-2c59-4acd-8c8f-d9e69fa95e84
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

def Polychromatic418967fa.branch_191_segment_000 : allB 134 191 :=
  allB_succ' 59 133 191 (Eq.refl Bool.true) (allA_of_3_0 59 133 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 132 191 (Eq.refl Bool.true) (allA_succ_of_accept 59 132 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 191 (accept_3_2 58 132 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 57
  132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 191 (accept_3_2 55 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 191 (Polychromatic418967fa.accept_17_3_13_4_1_8530 54 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 191 (accept_3_2 52 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 191 (accept_3_2 49 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 191 (Polychromatic418967fa.accept_23_1_17_7_1_11096 47 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 191 (accept_3_2 46 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 191 (accept_3_2 43 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 191 (accept_3_2 40 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 191 (accept_3_2 37 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 191 (accept_3_2 34 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 191 (accept_3_2 31 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 191 (accept_3_2 28 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 191 (accept_3_2 25 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 191 (accept_3_2 22 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 191
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 191 (accept_3_2 19 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 191 (accept_3_2 16 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 191 (accept_3_2 13 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 191 (accept_3_2 10 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 191 (accept_3_2 7 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 191 (accept_3_2 4 132 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 191
  (Polychromatic418967fa.accept_19_2_18_1_1_8275 2 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 191 (accept_3_2 1 132 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 131 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 131 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 191 (accept_3_2 58 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 57
  131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 191
  (Polychromatic418967fa.accept_19_18_17_1_1_2789 56 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 131 191 (accept_3_2 55 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 131 191 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 131 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 191 (accept_3_2 52 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 191 (Polychromatic418967fa.accept_9_6_5_2_1_421
  51 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 191
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 50 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 191 (accept_3_2 49 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 191 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 191 (accept_3_2 46 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 191
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 191 (accept_3_2 43 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 191 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 191 (accept_3_2 40 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 191 (accept_3_2 37 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 191 (accept_3_2 34 131 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 191 (accept_3_2 31 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 191 (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 191 (accept_3_2 28 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 131
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 191 (accept_3_2 25 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 191 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 191 (accept_3_2 22 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 191
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 191 (accept_3_2 19 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 191 (accept_3_2 16 131 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 191
  (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 191 (accept_3_2 13 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 191 (accept_3_2 10 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 191 (Polychromatic418967fa.accept_17_9_12_4_1_3468
  9 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 191 (accept_3_2 7 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 191 (accept_3_2 4 131 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 191
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 191 (accept_3_2 1 131 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 130 191 (Eq.refl Bool.true)
  (allA_of_3_0 62 130 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 129 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 191 (accept_3_2 61 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 191 (Polychromatic418967fa.accept_9_5_3_2_1_171
  59 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 191 (accept_3_2 58
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 191 (accept_3_2 55 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 191 (Polychromatic418967fa.accept_9_8_3_2_1_417
  53 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 191 (accept_3_2 52
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 191
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 191 (accept_3_2 49 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 191 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 191 (accept_3_2 46
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 191 (accept_3_2 43 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 191 (Polychromatic418967fa.accept_7_6_3_2_1_461
  41 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 191 (accept_3_2 40
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 191
  (Polychromatic418967fa.accept_12_3_9_11_1_231 39 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 191 (accept_3_2 37 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 191 (Polychromatic418967fa.accept_9_8_3_2_1_417
  35 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 191 (accept_3_2 34
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 191 (accept_3_2 31 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 191 (accept_3_2 28
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 191 (accept_3_2 25 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 191 (Polychromatic418967fa.accept_9_5_3_2_1_171
  23 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 191 (accept_3_2 22
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 191
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 191 (accept_3_2 19 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 191 (Polychromatic418967fa.accept_9_8_3_2_1_417
  17 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 191 (accept_3_2 16
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 191 (accept_3_2 13 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 191 (accept_3_2 10 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 129 191 (Polychromatic418967fa.accept_21_9_3_2_1_6363 9 129 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 191 (accept_3_2 7 129 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 191 (accept_3_2 4 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 191 (accept_3_2 1 129 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  128 191 (Eq.refl Bool.true) (allA_succ_of_accept 63 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 191 (accept_3_2 61 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 191 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 191 (accept_3_2 58 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 191
  (Polychromatic418967fa.accept_19_18_14_1_1_8323 56 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 191 (accept_3_2 55 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 128 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 191 (accept_3_2 52 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 191
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 128 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 128 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 191 (accept_3_2 49 128 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 128 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 48 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 191
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 191 (accept_3_2 46 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 44 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 191 (accept_3_2 43 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 191 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 191
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 191 (accept_3_2 40 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 191 (accept_3_2 37 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 191
  (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 191 (accept_3_2 34 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 191 (accept_3_2 31 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 191
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 191 (accept_3_2 28 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 191 (accept_3_2 25 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 191 (Polychromatic418967fa.accept_23_1_13_7_1_9355 24 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 191
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 191 (accept_3_2 22 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 191 (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 191 (accept_3_2 19 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 191
  (Polychromatic418967fa.accept_18_17_2_11_1_9749 17 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 128 191 (accept_3_2 16 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 191 (accept_3_2 13 128
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 191
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 191 (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 191 (accept_3_2 10 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 191
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 191 (accept_3_2 7 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 191 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 191 (accept_3_2 4 128 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 191 (accept_3_2 1 128 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 127 191 (Eq.refl Bool.true)
  (allA_of_3_0 65 127 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 126 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 191 (accept_3_2 64 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 126 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 191 (accept_3_2 61 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 126 191 (Polychromatic418967fa.accept_23_14_11_7_1_9410 60 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 126 191 (Polychromatic418967fa.accept_17_8_7_4_1_8617 59 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 191 (accept_3_2 58 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 191
  (Polychromatic418967fa.accept_19_18_12_1_1_9737 56 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 126 191 (accept_3_2 55 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 126 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 191 (accept_3_2 52 126 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 191
  (Polychromatic418967fa.accept_19_13_12_1_1_3993 51 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 126 191 (Polychromatic418967fa.accept_15_5_6_11_1_854 50 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 191 (accept_3_2 49 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 191
  (Polychromatic418967fa.accept_10_7_6_1_1_486 47 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 126 191 (accept_3_2 46 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 126 191 (Polychromatic418967fa.accept_25_19_1_16_1_11095 44 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 191 (accept_3_2 43 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 191 (accept_3_2 40 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 126 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 126 191 (Polychromatic418967fa.accept_25_13_1_16_1_9204 38 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 191 (accept_3_2 37 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 191 (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 191
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 191 (accept_3_2 34 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 126 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 191 (accept_3_2 31 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 191 (Polychromatic418967fa.accept_19_11_12_1_1_11049 30
  126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 191 (accept_3_2 28 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 126 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 126 191 (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 191 (accept_3_2 25 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 191
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 23 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 126 191 (accept_3_2 22 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 191 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 191 (accept_3_2 19 126
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 191
  (Polychromatic418967fa.accept_15_3_6_11_1_855 18 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 191 (accept_3_2 16 126 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 191
  (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 191 (accept_3_2 13 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 191 (Polychromatic418967fa.accept_19_11_12_1_1_11049 11 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 191 (accept_3_2 10 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 191
  (Polychromatic418967fa.accept_17_8_7_4_1_8617 8 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 191 (accept_3_2 7 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 191 (Polychromatic418967fa.accept_25_6_1_16_1_11094 6 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 191 (accept_3_2 4 126 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 126 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 191 (accept_3_2 1 126 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 125 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 191 (Polychromatic418967fa.accept_19_8_11_1_1_8320 65 125
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 191 (accept_3_2 64 125
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 191 (accept_3_2 61 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 125 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 191 (accept_3_2 58
  125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 125 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 191 (accept_3_2 55 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 191 (Polychromatic418967fa.accept_7_4_6_2_1_451
  53 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 191 (accept_3_2 52
  125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 191
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 191 (accept_3_2 49 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 125 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 191 (accept_3_2 46 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 191 (accept_3_2 43 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 191 (accept_3_2 40 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 191 (accept_3_2 37 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 191
  (Polychromatic418967fa.accept_16_3_13_15_1_1913 35 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 125 191 (accept_3_2 34 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 125 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 125 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 191 (accept_3_2 31 125 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 191 (accept_3_2 28 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 191 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 191 (accept_3_2 25 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 191 (accept_3_2 22 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 191 (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 191 (accept_3_2 19 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 191 (accept_3_2 16 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 191 (accept_3_2 13 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 191 (accept_3_2 10 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 191 (accept_3_2 7 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 191 (accept_3_2 4 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 191 (accept_3_2 1 125 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 124 191 (Eq.refl Bool.true) (allA_of_3_0 68 124 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 123 191
  (Eq.refl Bool.true) (allA_succ_of_accept 68 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 191 (accept_3_2 67 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 123 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 191
  (Polychromatic418967fa.accept_16_1_11_15_1_498 65 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 191 (accept_3_2 64 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 191 (Polychromatic418967fa.accept_18_9_15_11_1_5693 63 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 191 (accept_3_2 61 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 191 (accept_3_2 58 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 191 (accept_3_2 55 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 191 (accept_3_2 52 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 191 (accept_3_2 49 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 191 (accept_3_2 46 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 191 (accept_3_2 43 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 191 (accept_3_2 40 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 191 (accept_3_2 37 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 191 (accept_3_2 34 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 191 (accept_3_2 31 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 191
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 191 (accept_3_2 28 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 191 (accept_3_2 25 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 191 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 123 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 191 (accept_3_2 22 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 191 (accept_3_2 19 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 191 (accept_3_2 16 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 191 (accept_3_2 13 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 191
  (Polychromatic418967fa.accept_19_11_9_1_1_2809 11 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 191 (accept_3_2 10 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 191 (accept_3_2 7 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 191 (accept_3_2 4 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 191 (accept_3_2 1 123 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 122 191 (Eq.refl Bool.true) (allA_succ_of_accept 69 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 122 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 122 191 (accept_3_2 67 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 122 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 191 (accept_3_2 64 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 191 (accept_3_2 61 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 59 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 191 (accept_3_2 58 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 191 (accept_3_2 55 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 191 (accept_3_2 52 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 191 (accept_3_2 49 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 191 (accept_3_2 46 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 191 (accept_3_2 43 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 191 (accept_3_2 40 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 191
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 38 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 122 191 (accept_3_2 37 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 122 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 122 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 191 (accept_3_2 34 122 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 191 (accept_3_2 31 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 191 (accept_3_2 28 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 191 (accept_3_2 25 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 191 (accept_3_2 22 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 191 (accept_3_2 19 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 191 (Polychromatic418967fa.accept_19_18_8_1_1_11071 18 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 191 (accept_3_2 16 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 191
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 191 (accept_3_2 13 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 191 (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 191 (accept_3_2 10 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 191 (accept_3_2 7 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 191 (accept_3_2 4 122 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 191
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 191 (accept_3_2 1 122 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 121 191 (Eq.refl Bool.true)
  (allA_of_3_0 71 121 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 120 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 191 (accept_3_2 70 120 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 120 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 191 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 191 (accept_3_2 67
  120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 120 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 120 191 (Polychromatic418967fa.accept_16_1_8_15_1_1945 65 120 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 191 (accept_3_2 64 120 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 120 191 (Polychromatic418967fa.accept_18_9_12_11_1_5642 63 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 191 (accept_3_2 61 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 191 (accept_3_2 58 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 191 (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 191
  (Polychromatic418967fa.accept_17_5_1_4_1_3460 56 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 191 (accept_3_2 55 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 120 191 (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 120 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 191 (accept_3_2 52 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 191 (accept_3_2 49 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 191 (accept_3_2 46 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 120 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 191 (accept_3_2 43 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 191 (accept_3_2 40 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 191 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 120 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 191 (accept_3_2 37 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 191 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 191 (accept_3_2 34 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 191 (accept_3_2 31 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 191 (Polychromatic418967fa.accept_19_11_6_1_1_2826 30 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 191 (Polychromatic418967fa.accept_14_1_8_9_1_1312 29 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 191 (accept_3_2 28 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 191 (accept_3_2 25 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 191 (accept_3_2 22 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 191 (accept_3_2 19 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 191 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 191 (accept_3_2 16 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 191 (accept_3_2 13 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 191 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 191 (Polychromatic418967fa.accept_19_11_6_1_1_2826 11 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 191 (accept_3_2 10 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 191 (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 120
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 191 (accept_3_2 7 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 191 (accept_3_2 4 120 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 191
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 191 (accept_3_2 1 120 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 119 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 119 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 191 (Polychromatic418967fa.accept_13_6_2_9_1_1188 71 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 191 (accept_3_2 70 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 191
  (Polychromatic418967fa.accept_19_12_5_1_1_11093 69 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 191 (accept_3_2 67 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186 66 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 191 (accept_3_2 64 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 62 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 191 (accept_3_2 61 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 191 (Polychromatic418967fa.accept_19_3_5_1_1_6811 60 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 191
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 191 (accept_3_2 58 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 191 (Polychromatic418967fa.accept_16_8_7_15_1_6339 56 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 191 (accept_3_2 55 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 191 (Polychromatic418967fa.accept_14_12_7_9_1_726 54 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 191
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 191 (accept_3_2 52 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 191 (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 50 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 191 (accept_3_2 49 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 191
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 191 (accept_3_2 46 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 191 (accept_3_2 43 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 191
  (Polychromatic418967fa.accept_19_3_5_1_1_6811 41 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 191 (accept_3_2 40 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 191 (Polychromatic418967fa.accept_23_16_4_7_1_11092 39 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 191 (accept_3_2 37 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 191 (Polychromatic418967fa.accept_27_9_11_2_1_414 36 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 191 (accept_3_2 34 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 191 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 191 (accept_3_2 31 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 191
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 191 (accept_3_2 28 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 191 (Polychromatic418967fa.accept_14_12_7_9_1_726 26 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 191 (accept_3_2 25 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 191
  (Polychromatic418967fa.accept_19_4_5_1_1_4077 23 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 191 (accept_3_2 22 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 191 (Polychromatic418967fa.accept_25_21_19_16_1_11091 21 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 191 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 191 (accept_3_2 19 119 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 191
  (Polychromatic418967fa.accept_21_17_14_2_1_4762 17 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 119 191 (accept_3_2 16 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 191 (accept_3_2 13 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 191
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 191 (accept_3_2 10 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 191 (Polychromatic418967fa.accept_19_9_5_1_1_2766 9 119 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 8
  119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 191 (accept_3_2 7 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 191
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 191 (accept_3_2 4 119 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 119 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 2
  119 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 191 (accept_3_2 1 119
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 118 191 (Eq.refl
  Bool.true) (allA_of_3_0 74 118 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 117 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 191 (accept_3_2 73 117 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 117 191 (Polychromatic418967fa.accept_21_9_12_2_1_4781 72 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 191
  (Polychromatic418967fa.accept_25_21_17_16_1_11090 71 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 117 191 (accept_3_2 70 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 117 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 117 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 191 (accept_3_2 67 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 191
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 191 (accept_3_2 64 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 191 (accept_3_2 61 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 191 (accept_3_2 58 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 191 (Polychromatic418967fa.accept_22_13_7_15_1_11089 57 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 191 (accept_3_2 55 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 191 (accept_3_2 52 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 191 (accept_3_2 49 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 191 (Polychromatic418967fa.accept_18_12_9_11_1_4370 48 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 191
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 191 (accept_3_2 46 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 191 (accept_3_2 43 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 191
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 191 (accept_3_2 40 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 191 (accept_3_2 37 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 191
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 191 (accept_3_2 34 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 191 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 191 (accept_3_2 31 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 191
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 191 (accept_3_2 28 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 117 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 117 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 191 (accept_3_2 25 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24
  117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 191
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 191 (accept_3_2 22 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 191 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 117 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 191 (accept_3_2 19 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 191 (accept_3_2 16 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 191 (accept_3_2 13 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 191 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 117 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 191 (accept_3_2 10 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 191 (Polychromatic418967fa.accept_21_9_12_2_1_4781 9 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 191 (accept_3_2 7 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 191
  (Polychromatic418967fa.accept_19_5_3_1_1_4055 5 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 191 (accept_3_2 4 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 191 (accept_3_2 1 117 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 116 191 (Eq.refl Bool.true) (allA_succ_of_accept 75 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32
  75 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 116 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 116 191 (accept_3_2 73 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 116 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 116 191 (Polychromatic418967fa.accept_19_14_2_1_1_8308 71 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 116 191 (accept_3_2 70 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 116 191 (accept_3_2 67 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 116 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 116 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 191 (accept_3_2 64 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 116 191 (accept_3_2 61 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 116 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 116 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 191 (accept_3_2 58 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 191
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 191 (accept_3_2 55 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 191 (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 191 (accept_3_2 52 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 191 (accept_3_2 49 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 191 (accept_3_2 46 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 191
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 191 (accept_3_2 43 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 191 (accept_3_2 40 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 191 (accept_3_2 37 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 191 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 191 (accept_3_2 34 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 191 (accept_3_2 31 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 191 (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 191 (accept_3_2 28 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 191 (accept_3_2 25 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 191 (accept_3_2 22 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 191 (accept_3_2 19 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 191 (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 191 (accept_3_2 16 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 191 (accept_3_2 13 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 191 (accept_3_2 10 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 191
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 191 (accept_3_2 7 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 191 (accept_3_2 4 116 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 191 (accept_3_2 1 116 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 115 191 (Eq.refl
  Bool.true) (allA_of_3_0 77 115 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 114 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 191 (accept_3_2 76 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092
  74 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 191 (accept_3_2 73
  114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 191
  (Polychromatic418967fa.accept_23_3_22_7_1_2739 72 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 114 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 191 (accept_3_2 70 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 191 (Polychromatic418967fa.accept_9_5_6_2_1_161
  68 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 191 (accept_3_2 67
  114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 191
  (Polychromatic418967fa.accept_9_3_6_2_1_160 66 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 191 (accept_3_2 64 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 191 (Polychromatic418967fa.accept_14_7_2_9_1_2093 63 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 191 (accept_3_2 61 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 191 (accept_3_2 58 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 191
  (Polychromatic418967fa.accept_21_14_9_2_1_8005 56 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 191 (accept_3_2 55 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 191 (Polychromatic418967fa.accept_21_12_9_2_1_7941 54 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 191 (accept_3_2 52 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 191 (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 114 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 191 (accept_3_2 49 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 191 (accept_3_2 46 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 191 (accept_3_2 43 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 191 (Polychromatic418967fa.accept_17_8_12_4_1_2525 42 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 191 (accept_3_2 40 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 191
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 114 191 (accept_3_2 37 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 114 191 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 114 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 191 (accept_3_2 34 114 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 191 (accept_3_2 31 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 191 (accept_3_2 28 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 191 (accept_3_2 25 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 191 (Polychromatic418967fa.accept_17_7_12_4_1_2524 24 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 191 (accept_3_2 22 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 191
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 191 (accept_3_2 19 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 191 (accept_3_2 16 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 191 (accept_3_2 13 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 191 (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 191 (accept_3_2 10 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 191 (accept_3_2 7 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 191 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 191 (accept_3_2 4 114 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 114 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 191
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 191 (accept_3_2 1 114 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 113 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 191
  (Polychromatic418967fa.accept_21_14_8_2_1_11088 77 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 113 191 (accept_3_2 76 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 113 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 113 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 191 (accept_3_2 73 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 191 (Polychromatic418967fa.accept_10_2_3_1_1_481
  72 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 191 (accept_3_2 70 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 68 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 191 (accept_3_2 67 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 191 (accept_3_2 64 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 191 (accept_3_2 61 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 191 (accept_3_2 58 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 191 (Polychromatic418967fa.accept_16_8_1_15_1_1982 56 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 191 (accept_3_2 55 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 191 (accept_3_2 52 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 191 (accept_3_2 49 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 191
  (Polychromatic418967fa.accept_21_5_8_2_1_11063 47 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 191 (accept_3_2 46 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 191 (accept_3_2 43 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 191 (accept_3_2 40 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 191 (accept_3_2 37 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 191 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 191 (accept_3_2 34 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 191 (accept_3_2 31 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 191
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 191 (accept_3_2 28 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 191 (accept_3_2 25 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 191
  (Polychromatic418967fa.accept_17_6_11_4_1_1525 23 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 191 (accept_3_2 22 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 191 (accept_3_2 19 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 191 (accept_3_2 16 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 191 (accept_3_2 13 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 113 191 (accept_3_2 10 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 113 191 (Polychromatic418967fa.accept_22_9_3_15_1_4527 9 113 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 191 (accept_3_2 7 113 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 191 (accept_3_2 4 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 191 (accept_3_2 1 113 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 112 191 (Eq.refl Bool.true) (allA_of_3_0 80 112 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 111 191 (Eq.refl Bool.true) (allA_succ_of_accept 80 111 191 (Polychromatic418967fa.accept_6_2_3_5_1_26
  80 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 191 (accept_3_2 79
  111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 111 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 191 (accept_3_2 76 111 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 191 (Polychromatic418967fa.accept_21_12_6_2_1_7950 75 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 191 (accept_3_2 73 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 111 191 (Polychromatic418967fa.accept_19_15_16_1_1_11087 72 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 191 (accept_3_2 70 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 191 (accept_3_2 67 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 111 191 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 191 (accept_3_2 64 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 111
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 191 (accept_3_2 61 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 191 (accept_3_2 58 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 191 (accept_3_2 55 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 191 (accept_3_2 52 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 191 (accept_3_2 49 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 191 (accept_3_2 46 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 111 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 191 (accept_3_2 43 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 191 (accept_3_2 40 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 191 (accept_3_2 37 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 191 (accept_3_2 34 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 191 (accept_3_2 31 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 191 (accept_3_2 28 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 191 (Polychromatic418967fa.accept_19_8_16_1_1_11051 27 111 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 191 (accept_3_2 25 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 191 (accept_3_2 22 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 191 (accept_3_2 19 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 191 (accept_3_2 16 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 191 (accept_3_2 13 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 191 (Polychromatic418967fa.accept_17_12_9_4_1_5982 12 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 191 (accept_3_2 10 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 191 (accept_3_2 7 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 191 (accept_3_2 4 111 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 191 (accept_3_2 1 111 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 110 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 110 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 191 (accept_3_2 79
  110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 191
  (Polychromatic418967fa.accept_19_2_15_1_1_3977 78 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 110 191 (accept_3_2 76 110 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 110 191 (Polychromatic418967fa.accept_7_4_5_2_1_243
  74 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 191 (accept_3_2 73
  110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 191
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 110 191 (Polychromatic418967fa.accept_16_7_14_15_1_2932 71 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 110 191 (accept_3_2 70 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 110 191 (accept_3_2 67 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 191 (accept_3_2 64 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 191
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 191 (accept_3_2 61 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 191 (accept_3_2 58 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 191 (accept_3_2 55 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 191 (accept_3_2 52 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 191
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 50 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 110 191 (accept_3_2 49 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 110 191 (Polychromatic418967fa.accept_23_2_18_7_1_11086 48 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 191 (accept_3_2 46 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 191 (accept_3_2 43 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 191 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 110
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 191 (accept_3_2 40 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 191 (accept_3_2 37 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 191 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 110 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 191
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 191 (accept_3_2 34 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 191 (accept_3_2 31 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 191 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 191 (accept_3_2 28 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 191 (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 191 (accept_3_2 25 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 191
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 191 (accept_3_2 22 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 191 (accept_3_2 19 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 191 (accept_3_2 16 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 191 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 191 (accept_3_2 13 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 191 (Polychromatic418967fa.accept_17_12_8_4_1_2518 12 110
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 191 (accept_3_2 10 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 191 (accept_3_2 7 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 191 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 110 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 191 (accept_3_2 4 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 191 (accept_3_2 1 110 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 109 191 (Eq.refl
  Bool.true) (allA_of_3_0 83 109 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 108 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 108 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 191 (accept_3_2 82 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 108 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 191
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 80 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 191 (accept_3_2 79 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 191 (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 191 (accept_3_2 76 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 191
  (Polychromatic418967fa.accept_15_14_3_11_1_850 74 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 191 (accept_3_2 73 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 108 191 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 191 (accept_3_2 70 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 191 (accept_3_2 67 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 191 (Polychromatic418967fa.accept_19_8_13_1_1_8221 65 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 191 (accept_3_2 64 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 191 (accept_3_2 61 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 191 (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 191 (accept_3_2 58 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 191
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 108 191 (accept_3_2 55 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 191 (accept_3_2 52 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 191 (accept_3_2 49 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 191 (accept_3_2 46
  108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 191
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 44 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 191 (accept_3_2 43 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 191 (Polychromatic418967fa.accept_23_19_16_7_1_7760 42 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 191 (accept_3_2 40 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 108 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 108 191 (Polychromatic418967fa.accept_15_8_3_11_1_849 38 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 191 (accept_3_2 37 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 191 (accept_3_2 34 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 108 191 (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 191 (accept_3_2 31 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 191 (Polychromatic418967fa.accept_21_9_3_2_1_6363 30 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 191 (accept_3_2 28 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 191 (accept_3_2 25 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 191
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 191 (accept_3_2 22 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 191 (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 191 (accept_3_2 19 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 108 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 191
  (Polychromatic418967fa.accept_20_17_8_11_1_6615 17 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 108 191 (accept_3_2 16 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 191 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 191 (accept_3_2 13 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 191 (accept_3_2 10 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 8
  108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 191 (accept_3_2 7 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 191 (accept_3_2 4 108 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 2
  108 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 191 (accept_3_2 1 108
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 107 191
  (Eq.refl Bool.true) (allA_succ_of_accept 84 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 191
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 83 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 191 (accept_3_2 82 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 191 (Polychromatic418967fa.accept_15_6_2_11_1_325 81 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 191 (Polychromatic418967fa.accept_13_2_3_9_1_2610 80 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 191 (accept_3_2 79 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 191 (accept_3_2 76 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 74 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 191 (accept_3_2 73 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 191 (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 107
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 191
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 71 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 191 (accept_3_2 70 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 191 (accept_3_2 67 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 191 (accept_3_2 64 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 191 (Polychromatic418967fa.accept_23_17_15_7_1_11085 63 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 62 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 191 (accept_3_2 61 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 191 (accept_3_2 58 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 191 (accept_3_2 55 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 107
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 191
  (Polychromatic418967fa.accept_24_5_11_23_1_7419 53 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 107 191 (accept_3_2 52 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 107 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 191 (accept_3_2 49 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162
  48 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 191
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 191 (accept_3_2 46 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 191 (accept_3_2 43 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 191 (accept_3_2 40 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 191 (Polychromatic418967fa.accept_13_12_3_9_1_4341 38 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 191 (accept_3_2 37 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 191 (accept_3_2 34 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 191 (accept_3_2 31 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 191
  (Polychromatic418967fa.accept_11_7_8_4_1_718 29 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 191 (accept_3_2 28 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 191 (Polychromatic418967fa.accept_19_8_12_1_1_11084 27 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 191 (accept_3_2 25 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 191 (accept_3_2 22 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 191 (accept_3_2 19 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 191
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 191 (accept_3_2 16 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 191 (accept_3_2 13 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 191
  (Polychromatic418967fa.accept_19_11_12_1_1_11049 11 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 107 191 (accept_3_2 10 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 107 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 107 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 191 (accept_3_2 7 107 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 191 (accept_3_2 4 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 107 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 191 (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 191 (accept_3_2 1 107 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 106 191
  (Eq.refl Bool.true) (allA_of_3_0 86 106 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 105 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 191 (accept_3_2 85 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 191
  (Polychromatic418967fa.accept_13_5_1_9_1_618 83 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 191 (accept_3_2 82 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 191 (Polychromatic418967fa.accept_17_13_3_4_1_2537 81 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 191 (accept_3_2 79 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 191 (accept_3_2 76 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 191 (accept_3_2 73 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 191 (accept_3_2 70 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 191 (accept_3_2 67 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 191
  (Polychromatic418967fa.accept_23_19_13_7_1_11083 65 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 105 191 (accept_3_2 64 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 105 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 191 (accept_3_2 61 105 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 191 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  60 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 191 (accept_3_2 58 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 191 (accept_3_2 55 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 191 (accept_3_2 52 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 191 (accept_3_2 49 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 191
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 191 (accept_3_2 46 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 191 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 191 (accept_3_2 43 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 191 (accept_3_2 40 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 191 (accept_3_2 37 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 191 (accept_3_2 34 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 191 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 191 (accept_3_2 31 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 191 (accept_3_2 28 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 191 (accept_3_2 25 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 191 (accept_3_2 22 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 191 (accept_3_2 19 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 191 (accept_3_2 16 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 191 (accept_3_2 13 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 191
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 191 (accept_3_2 10 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 191 (accept_3_2 7 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 191 (accept_3_2 4 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 191 (accept_3_2 1 105 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 104 191
  (Eq.refl Bool.true) (allA_succ_of_accept 87 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 104 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 104 191 (accept_3_2 85 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 104 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 104 191 (Polychromatic418967fa.accept_17_15_2_4_1_2423 83 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 104 191 (accept_3_2 82 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 104 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 104 191 (accept_3_2 79 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 104 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 104 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 104 191 (accept_3_2 76 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 191 (accept_3_2 73 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 191 (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 191 (accept_3_2 70 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 191
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 68 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 191 (accept_3_2 67 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 65 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 191 (accept_3_2 64 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 191 (accept_3_2 61 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 191 (accept_3_2 58 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 191
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 56 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 104 191 (accept_3_2 55 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 104 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 104 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 191 (accept_3_2 52 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 191 (accept_3_2 49 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 191 (accept_3_2 46 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 191 (accept_3_2 43 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 191 (Polychromatic418967fa.accept_16_9_8_15_1_5095 41 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 191 (accept_3_2 40 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 191 (accept_3_2 37 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 191 (accept_3_2 34 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 191 (accept_3_2 31 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 191 (accept_3_2 28 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 191 (accept_3_2 25 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 191 (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 191 (accept_3_2 22 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 191
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 191 (accept_3_2 19 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 191 (accept_3_2 16 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 191 (accept_3_2 13 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 191 (accept_3_2 10 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 191 (accept_3_2 7 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 191 (accept_3_2 4 104 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 191 (accept_3_2 1 104 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 103 191
  (Eq.refl Bool.true) (allA_of_3_0 89 103 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 102 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 191 (accept_3_2 88 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 191 (accept_3_2 85 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 102 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 84 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 102 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 191 (accept_3_2 82 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 102 191 (accept_3_2 79 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 191 (accept_3_2 76 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 102 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 191
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 74 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 102 191 (accept_3_2 73 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 102 191 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 102 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 102 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 191 (accept_3_2 70 102 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 191 (accept_3_2 67 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 191 (accept_3_2 64 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 191 (accept_3_2 61 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 102 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 191 (accept_3_2 58 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 191 (accept_3_2 55 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 191 (accept_3_2 52 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 191 (accept_3_2 49 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 191 (accept_3_2 46 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 191 (accept_3_2 43 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 191 (accept_3_2 40 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 191
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 102 191 (accept_3_2 37 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 102 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 191 (accept_3_2 34 102 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 191 (accept_3_2 31 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 191 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 191 (accept_3_2 28 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 191 (accept_3_2 25 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 191 (accept_3_2 22 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 191 (accept_3_2 19 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 191 (accept_3_2 16 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 191 (accept_3_2 13 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 191 (Polychromatic418967fa.accept_25_11_2_16_1_11082 11 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 191 (accept_3_2 10 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 191 (accept_3_2 7 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 191 (accept_3_2 4 102 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 102 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 191
  (Polychromatic418967fa.accept_13_2_11_9_1_591 2 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 191 (accept_3_2 1 102 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 101 191
  (Eq.refl Bool.true) (allA_succ_of_accept 90 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 191 (accept_3_2 88 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 191 (Polychromatic418967fa.accept_19_11_6_1_1_2826 87 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 191 (accept_3_2 85 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 191 (Polychromatic418967fa.accept_13_6_10_9_1_4329 84 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 191 (accept_3_2 82 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 191 (Polychromatic418967fa.accept_16_1_5_15_1_2918 81 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 191 (Polychromatic418967fa.accept_22_14_13_15_1_9448 80 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 191 (accept_3_2 79 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 191
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 77 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 191 (accept_3_2 76 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 101 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 191 (accept_3_2 73 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  72 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 191 (accept_3_2 70 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 191 (accept_3_2 67 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 191
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 191 (accept_3_2 64 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 191 (Polychromatic418967fa.accept_24_15_5_23_1_9282 63 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 191 (accept_3_2 61 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 191 (Polychromatic418967fa.accept_19_3_6_1_1_4064 60 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 191
  (Polychromatic418967fa.accept_19_2_6_1_1_9729 59 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 191 (accept_3_2 58 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 191 (Polychromatic418967fa.accept_17_5_16_4_1_4734 56 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 191 (accept_3_2 55 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 191
  (Polychromatic418967fa.accept_11_9_2_4_1_707 53 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 191 (accept_3_2 52 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 191 (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 191 (accept_3_2 49 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 191 (accept_3_2 46 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 191 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 191 (Polychromatic418967fa.accept_20_4_1_11_1_9646 44 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 191 (accept_3_2 43 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 191 (accept_3_2 40 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 191 (accept_3_2 37 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 191
  (Polychromatic418967fa.accept_21_14_17_2_1_11069 35 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 101 191 (accept_3_2 34 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 101 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 191 (Polychromatic418967fa.accept_13_6_10_9_1_4329 32 101
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 191 (accept_3_2 31 101
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 101 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 191 (accept_3_2 28 101 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 101 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 191 (accept_3_2 25
  101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 191
  (Polychromatic418967fa.accept_19_5_6_1_1_5366 24 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 101 191 (Polychromatic418967fa.accept_25_23_1_16_1_11081 23 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 191 (accept_3_2 22 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 191 (Polychromatic418967fa.accept_19_2_6_1_1_9729 21 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 191 (accept_3_2 19 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 191 (accept_3_2 16 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 191 (accept_3_2 13 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 191 (Polychromatic418967fa.accept_19_11_6_1_1_2826 11 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 191 (accept_3_2 10 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 101 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 191 (accept_3_2 7 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 191 (accept_3_2 4 101 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 191 (Polychromatic418967fa.accept_17_3_16_4_1_2416 3 101 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 191 (accept_3_2 1 101 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 100 191
  (Eq.refl Bool.true) (allA_of_3_0 92 100 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 99 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 99 191 (accept_3_2 91 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 99 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 89 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 99 191 (accept_3_2 88 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  99 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 191 (accept_3_2 85 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 191 (accept_3_2 82 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  99 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 191 (accept_3_2 79 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 191
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 99 191 (accept_3_2 76 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  99 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 191 (accept_3_2 73 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 191
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 191 (accept_3_2 70 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  99 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 191 (accept_3_2 67 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 191 (accept_3_2 64 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  99 191 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 191 (accept_3_2 61 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 191 (accept_3_2 58 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  99 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 191 (accept_3_2 55 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 191 (Polychromatic418967fa.accept_19_16_4_1_1_5376 54 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 191
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 191 (accept_3_2 52 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 191 (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 191 (accept_3_2 49 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 191
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 191 (accept_3_2 46 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 191 (accept_3_2 43 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 191 (accept_3_2 40 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 191 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 191 (accept_3_2 37 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 191 (accept_3_2 34 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 191 (accept_3_2 31 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 191 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 191
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 191 (accept_3_2 28 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 191 (accept_3_2 25 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 191
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 191 (accept_3_2 22 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 191 (accept_3_2 19 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 191 (accept_3_2 16 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 191 (accept_3_2 13 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 191 (accept_3_2 10 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 191 (accept_3_2 7 99 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 191 (accept_3_2 4 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 191 (accept_3_2 1 99 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 98 191
  (Eq.refl Bool.true) (allA_succ_of_accept 93 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 191 (accept_3_2 91 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 191 (Polychromatic418967fa.accept_21_6_14_2_1_7980 90 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 191 (accept_3_2 88 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 191 (accept_3_2 85 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 83 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 191 (accept_3_2 82 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 191 (accept_3_2 79 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 191 (accept_3_2 76 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 191
  (Polychromatic418967fa.accept_19_17_3_1_1_4056 74 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 191 (accept_3_2 73 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 191 (Polychromatic418967fa.accept_15_12_8_11_1_4383 72 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 71 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 191 (accept_3_2 70 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 191 (accept_3_2 67 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 191 (accept_3_2 64 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 191
  (Polychromatic418967fa.accept_19_5_3_1_1_4055 62 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 191 (accept_3_2 61 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 191 (accept_3_2 58 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 191 (accept_3_2 55 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 191 (accept_3_2 52 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 191 (accept_3_2 49 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 191 (accept_3_2 46 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 191 (accept_3_2 43 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 191 (accept_3_2 40 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 191
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 191 (accept_3_2 37 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 191 (Polychromatic418967fa.accept_19_17_3_1_1_4056 36 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 191 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 191 (accept_3_2 34 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 191 (accept_3_2 31 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 191 (accept_3_2 28 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 191
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 26 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 191 (accept_3_2 25 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 191 (accept_3_2 22 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 191 (accept_3_2 19 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 191 (accept_3_2 16 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 191 (accept_3_2 13 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 191 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 191 (accept_3_2 10 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 191 (accept_3_2 7 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 191 (accept_3_2 4 98 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2
  98 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 191 (accept_3_2 1 98 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 97
  191 (Eq.refl Bool.true) (allA_of_3_0 95 97 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 191
  (allA_succ_of_accept 95 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 191 (accept_3_2 94 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  92 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 191 (accept_3_2 91
  96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 191
  (Polychromatic418967fa.accept_21_6_12_2_1_4801 90 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 191 (accept_3_2 88 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 86
  96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 191 (accept_3_2 85 96
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 191
  (Polychromatic418967fa.accept_9_3_6_2_1_160 84 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 191 (Polychromatic418967fa.accept_17_15_11_4_1_7218 83 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 191 (accept_3_2 82 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 191 (accept_3_2 79 96
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 191
  (Polychromatic418967fa.accept_11_1_8_4_1_717 78 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 191 (accept_3_2 76 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 74
  96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 191 (accept_3_2 73 96
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 191 (accept_3_2 70 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 191 (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 68
  96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 191 (accept_3_2 67 96
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17
  66 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 191
  (Polychromatic418967fa.accept_10_5_6_1_1_836 65 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 191 (accept_3_2 64 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 191 (Polychromatic418967fa.accept_14_7_12_9_1_2926 63 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 191 (accept_3_2 61 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 191 (accept_3_2 58 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 56 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 191 (accept_3_2 55 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 191 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 191 (accept_3_2 52 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 191 (accept_3_2 49 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 191
  (Polychromatic418967fa.accept_10_7_6_1_1_486 47 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 191 (accept_3_2 46 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 191 (accept_3_2 43 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 191 (accept_3_2 40 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 191 (accept_3_2 37 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 191 (Polychromatic418967fa.accept_27_9_15_2_1_11080 36 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 191 (accept_3_2 34 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 191 (accept_3_2 31 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 191
  (Polychromatic418967fa.accept_11_7_8_4_1_718 29 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 191 (accept_3_2 28 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 191 (accept_3_2 25 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 191 (accept_3_2 22 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 191 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 191 (accept_3_2 19 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 191 (accept_3_2 16 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 191 (accept_3_2 13 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 191 (accept_3_2 10 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 191 (accept_3_2 7 96 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 191 (Polychromatic418967fa.accept_17_6_11_4_1_1525 6 96 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 191 (accept_3_2 4 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 191 (accept_3_2 1 96 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 191
  (allA_succ_of_accept 94 95 191 (accept_3_2 94 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 191 (Polychromatic418967fa.accept_15_2_5_11_1_1563 92 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 191 (accept_3_2 91 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 95 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 191 (accept_3_2 88 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 86 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 191 (accept_3_2 85 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 191 (accept_3_2 82 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 191 (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 191 (accept_3_2 79 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 191 (accept_3_2 76 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 74 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 191 (accept_3_2 73 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 191 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 191 (accept_3_2 70 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 191 (accept_3_2 67 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 191
  (Polychromatic418967fa.accept_20_5_15_11_1_3758 65 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 191 (accept_3_2 64 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 191 (accept_3_2 61 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 191 (accept_3_2 58 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 191 (accept_3_2 55 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 191 (accept_3_2 52 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 191 (Polychromatic418967fa.accept_18_14_5_11_1_5676 50 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 191 (accept_3_2 49 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 191 (accept_3_2 46 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 191 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 191 (accept_3_2 43 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 191 (accept_3_2 40 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 191 (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 191 (accept_3_2 37 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 191 (accept_3_2 34 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 191 (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 191 (accept_3_2 31 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 191 (accept_3_2 28 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 191 (accept_3_2 25 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 191
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 191 (accept_3_2 22 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 191 (accept_3_2 19 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 191 (accept_3_2 16 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 191 (accept_3_2 13 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 191
  (Polychromatic418967fa.accept_17_11_10_4_1_5955 11 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 191 (accept_3_2 10 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 191 (accept_3_2 7 95 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 191 (accept_3_2 4 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 191 (Polychromatic418967fa.accept_14_2_11_9_1_2925 2 95 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 191 (accept_3_2 1 95 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 191
  (allA_of_3_0 94 94 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 191 (allA_succ_of_accept 92 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 191 (accept_3_2 91 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 191 (accept_3_2 88 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 191 (accept_3_2 85 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 191 (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 83 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 191 (accept_3_2 82 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 191 (accept_3_2 79 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 191 (accept_3_2 76 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 191 (accept_3_2 73 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 191 (accept_3_2 70 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 191 (accept_3_2 67 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 65 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 191 (accept_3_2 64 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 191 (accept_3_2 61 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 191 (accept_3_2 58 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 191 (accept_3_2 55 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 191 (accept_3_2 52 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 191 (accept_3_2 49 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 191 (Polychromatic418967fa.accept_17_13_8_4_1_2514 47 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 191 (accept_3_2 46 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 191 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 93 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 191 (accept_3_2 43 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 191 (accept_3_2 40 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 191 (accept_3_2 37 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 191 (accept_3_2 34 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 191 (accept_3_2 31 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 191 (accept_3_2 28 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 191 (accept_3_2 25 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 191 (accept_3_2 22 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 191 (accept_3_2 19 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 191 (accept_3_2 16 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 191 (accept_3_2 13 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 191 (accept_3_2 10 93 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 191 (Polychromatic418967fa.accept_19_9_17_1_1_8325 9 93 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 191 (accept_3_2 7 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 191 (accept_3_2 4 93 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 191 (accept_3_2 1 93 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 191
  (allA_succ_of_accept 91 92 191 (accept_3_2 91 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 89 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 191 (accept_3_2 88 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 191 (accept_3_2 85 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 191 (Polychromatic418967fa.accept_13_6_1_9_1_619 84 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 191 (accept_3_2 82 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 191 (accept_3_2 79 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 191 (Polychromatic418967fa.accept_21_15_8_2_1_11079 78 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 191 (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 191 (accept_3_2 76 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 191 (accept_3_2 73 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 191 (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 191 (Polychromatic418967fa.accept_13_6_1_9_1_619 71 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 191 (accept_3_2 70 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 191
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 68 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 191 (accept_3_2 67 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 191 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 191 (accept_3_2 64 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 191 (accept_3_2 61 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 191 (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 191 (accept_3_2 58 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 191 (accept_3_2 55 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 191 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 191 (accept_3_2 52 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 191 (accept_3_2 49 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 191 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 191 (accept_3_2 46 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 191
  (Polychromatic418967fa.accept_13_5_1_9_1_618 44 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 191 (accept_3_2 43 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 191 (Polychromatic418967fa.accept_17_8_7_4_1_8617 42 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 191 (accept_3_2 40 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 191 (accept_3_2 37 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 191 (accept_3_2 34 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 191
  (Polychromatic418967fa.accept_13_6_1_9_1_619 32 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 191 (accept_3_2 31 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 191 (Polychromatic418967fa.accept_22_8_4_15_1_11078 30 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 191 (accept_3_2 28 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 191
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 191 (accept_3_2 25 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 191 (accept_3_2 22 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 191 (accept_3_2 19 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 191 (accept_3_2 16 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 191 (accept_3_2 13 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 191 (Polychromatic418967fa.accept_17_12_7_4_1_7231 12 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 191 (accept_3_2 10 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 191
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 191 (accept_3_2 7 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 92 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 191 (accept_3_2 4 92 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  92 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 191 (accept_3_2 1 92 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 191
  (allA_of_3_0 91 91 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 191 (allA_succ_of_accept 89 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 191 (accept_3_2 88 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 86 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 191 (accept_3_2 85 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 191 (Polychromatic418967fa.accept_17_16_5_4_1_2499 84 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 191
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 191 (accept_3_2 82 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 191 (accept_3_2 79 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 191 (accept_3_2 76 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 75 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 191 (accept_3_2 73 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 191 (accept_3_2 70 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 191 (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 191 (accept_3_2 67 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 191 (accept_3_2 64 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 63 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 191 (Polychromatic418967fa.accept_13_10_12_9_1_1837 62 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 191 (accept_3_2 61 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 191 (accept_3_2 58 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 191 (Polychromatic418967fa.accept_19_18_14_1_1_8323 56 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 191 (accept_3_2 55 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 191 (Polychromatic418967fa.accept_20_14_10_11_1_2393 54 90
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 191 (accept_3_2 52 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 191 (Polychromatic418967fa.accept_19_13_14_1_1_3996 51 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 191 (accept_3_2 49 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 191 (Polychromatic418967fa.accept_19_10_14_1_1_8296 48 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 191
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 191 (accept_3_2 46 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 44 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 191 (accept_3_2 43 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 191 (accept_3_2 40 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 191 (accept_3_2 37 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 191
  (Polychromatic418967fa.accept_17_1_5_4_1_8532 35 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 191 (accept_3_2 34 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 191 (accept_3_2 31 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 191 (Polychromatic418967fa.accept_16_14_10_15_1_3969 30 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 191 (accept_3_2 28 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 191 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 191 (Polychromatic418967fa.accept_24_2_18_23_1_11077 26 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 191 (accept_3_2 25 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 191
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 191 (accept_3_2 22 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 191 (accept_3_2 19 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 191 (accept_3_2 16 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 191 (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 191 (accept_3_2 13 90 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 191 (Polychromatic418967fa.accept_21_12_6_2_1_7950 12 90
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 191 (accept_3_2 10 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 191 (accept_3_2 7 90 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 90 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 191 (accept_3_2 4 90 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 191
  (Polychromatic418967fa.accept_19_2_14_1_1_11076 2 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 191 (accept_3_2 1 90 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 191
  (allA_succ_of_accept 88 89 191 (accept_3_2 88 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 191 (accept_3_2 85 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 191
  (Polychromatic418967fa.accept_19_7_13_1_1_6804 83 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 191 (accept_3_2 82 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 191 (accept_3_2 79 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 191 (accept_3_2 76 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 191 (accept_3_2 73 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 191
  (Polychromatic418967fa.accept_19_14_13_1_1_11075 71 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 89 191 (accept_3_2 70 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 89 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 89 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 191 (accept_3_2 67 89 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 191 (accept_3_2 64 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 191 (accept_3_2 61 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 191 (accept_3_2 58 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 191 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 191 (accept_3_2 55 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 191 (accept_3_2 52 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 191 (accept_3_2 49 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 191
  (Polychromatic418967fa.accept_13_8_11_9_1_593 47 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 191 (accept_3_2 46 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 191 (Polychromatic418967fa.accept_26_18_11_9_1_11074 44 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 191 (accept_3_2 43 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 191 (accept_3_2 40 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 191 (accept_3_2 37 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 191 (Polychromatic418967fa.accept_22_14_1_15_1_6055 36 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 191
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 191 (accept_3_2 34 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 191 (accept_3_2 31 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 191
  (Polychromatic418967fa.accept_19_10_13_1_1_8264 29 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 191 (accept_3_2 28 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 191 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 191 (accept_3_2 25 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 191 (accept_3_2 22 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 191 (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 191 (accept_3_2 19 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 191 (accept_3_2 16 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 191 (accept_3_2 13 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 191 (accept_3_2 10 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 191 (Polychromatic418967fa.accept_22_9_1_15_1_9461 9 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 191 (accept_3_2 7 89 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 191 (accept_3_2 4 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 191 (accept_3_2 1 89 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 191 (allA_of_3_0 88 88 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 191
  (allA_succ_of_accept 86 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 191 (accept_3_2 85 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 83
  87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 191 (accept_3_2 82 87
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 191
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 191 (accept_3_2 79 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 77
  87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 191 (accept_3_2 76 87
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 191 (accept_3_2 73 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 191 (Polychromatic418967fa.accept_16_8_7_15_1_6339 72 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 191 (accept_3_2 70 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 191 (accept_3_2 67 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 191
  (Polychromatic418967fa.accept_19_8_11_1_1_8320 65 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 191 (accept_3_2 64 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 191 (Polychromatic418967fa.accept_17_12_2_4_1_11050 63 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 191 (accept_3_2 61 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 191 (accept_3_2 58 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 191 (accept_3_2 55 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 191 (accept_3_2 52 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 191 (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 191 (accept_3_2 49 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 191 (accept_3_2 46 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 191 (accept_3_2 43 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 191 (Polychromatic418967fa.accept_18_6_15_11_1_3141 42 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 191 (accept_3_2 40 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 191 (accept_3_2 37 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 191 (accept_3_2 34 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 191 (accept_3_2 31 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 191 (accept_3_2 28 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 191 (accept_3_2 25 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 191 (accept_3_2 22 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 191 (accept_3_2 19 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 191 (Polychromatic418967fa.accept_19_18_11_1_1_4035 18 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 191 (accept_3_2 16 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 191 (accept_3_2 13 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 191
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 191 (accept_3_2 10 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 191 (accept_3_2 7 87 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 191 (accept_3_2 4 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 191 (accept_3_2 1 87 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 191 (allA_succ_of_accept 85 86 191 (accept_3_2 85 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 86 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 191 (Polychromatic418967fa.accept_19_7_10_1_1_5382 83 86
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 191 (accept_3_2 82 86 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 81
  86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 191 (accept_3_2 79 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 191 (accept_3_2 76 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 191
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 74 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 191 (accept_3_2 73 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 191 (accept_3_2 70 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 191
  (Polychromatic418967fa.accept_11_2_9_4_1_310 68 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 191 (accept_3_2 67 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 191 (accept_3_2 64 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 191 (accept_3_2 61 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 191 (Polychromatic418967fa.accept_13_7_8_9_1_1158 59 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 191 (accept_3_2 58 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 191 (accept_3_2 55 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 191 (Polychromatic418967fa.accept_19_16_10_1_1_11073 54 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 191 (accept_3_2 52 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 191 (accept_3_2 49 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 191 (accept_3_2 46 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 191 (accept_3_2 43 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 191 (accept_3_2 40 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 191
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 191 (accept_3_2 37 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 191 (Polychromatic418967fa.accept_19_17_10_1_1_6795 36 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 191 (accept_3_2 34 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 191 (accept_3_2 31 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 191 (accept_3_2 28 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 191 (accept_3_2 25 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 191 (Polychromatic418967fa.accept_16_7_6_15_1_495 23 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 191 (accept_3_2 22 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 191 (accept_3_2 19 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 191 (accept_3_2 16 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 191
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 191 (accept_3_2 13 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 191 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 191 (accept_3_2 10 86 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 191 (accept_3_2 7 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 191 (accept_3_2 4 86 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  86 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 191 (accept_3_2 1 86 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 191
  (allA_of_3_0 85 85 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 191 (allA_succ_of_accept 83 84 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 191 (accept_3_2 82 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 191 (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 191 (accept_3_2 79 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 191 (accept_3_2 76 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 74 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 191 (accept_3_2 73 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 191 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 191 (accept_3_2 70 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 191 (accept_3_2 67 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 191 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 191
  (Polychromatic418967fa.accept_10_5_4_1_1_842 65 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 191 (accept_3_2 64 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 191 (accept_3_2 61 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 191 (accept_3_2 58 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 191 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 191 (accept_3_2 55 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 191 (accept_3_2 52 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 191 (accept_3_2 49 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 191 (Polychromatic418967fa.accept_23_2_15_7_1_11042 48 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 191
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 191 (accept_3_2 46 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 191 (accept_3_2 43 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 191 (accept_3_2 40 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 191 (Polychromatic418967fa.accept_17_5_16_4_1_4734 39 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 191 (Polychromatic418967fa.accept_27_11_3_2_1_11072 38 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 191 (accept_3_2 37 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 84 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 191 (accept_3_2 34 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 191 (accept_3_2 31 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 191
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 191 (accept_3_2 28 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 191 (accept_3_2 25 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 191 (accept_3_2 22 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 191 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 191 (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 191 (accept_3_2 19 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 191 (Polychromatic418967fa.accept_19_18_8_1_1_11071 18 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 191 (accept_3_2 16 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 191 (accept_3_2 13 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 191 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 191 (accept_3_2 10 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 191 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 191 (accept_3_2 7 84 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 191 (accept_3_2 4 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  191 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 84 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 191 (accept_3_2 1 84 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 191 (allA_succ_of_accept 82 83 191 (accept_3_2 82 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 83 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 191 (accept_3_2 79 83 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 78
  83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 191
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 77 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 191 (accept_3_2 76 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 191 (accept_3_2 73 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 191 (accept_3_2 70 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 191 (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 191 (accept_3_2 67 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 191 (accept_3_2 64 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 62 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 191 (accept_3_2 61 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 191 (accept_3_2 58 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 191 (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 191 (accept_3_2 55 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 191 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 191 (accept_3_2 52 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 191 (Polychromatic418967fa.accept_19_13_7_1_1_5379 51 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 191 (accept_3_2 49 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 191
  (Polychromatic418967fa.accept_21_5_20_2_1_7948 47 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 191 (accept_3_2 46 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 191 (accept_3_2 43 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 191
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 191 (accept_3_2 40 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 191 (accept_3_2 37 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 191
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 191 (accept_3_2 34 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 33 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 191 (accept_3_2 31 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 191 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 191 (accept_3_2 28 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 191 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 191 (Polychromatic418967fa.accept_21_5_20_2_1_7948 26 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 191 (accept_3_2 25 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 191
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 191 (accept_3_2 22 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 191 (Polychromatic418967fa.accept_19_2_7_1_1_2808 21 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 191 (accept_3_2 19 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 191 (accept_3_2 16 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 191 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 191 (accept_3_2 13 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 191 (accept_3_2 10 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 191 (Polychromatic418967fa.accept_21_9_20_2_1_8000 9 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 191 (accept_3_2 7 83 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 191 (Polychromatic418967fa.accept_19_6_7_1_1_2805 6 83 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 191 (accept_3_2 4 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 83 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 191 (accept_3_2 1 83 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 191 (allA_of_3_0 82 82 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 191
  (allA_succ_of_accept 80 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 191 (accept_3_2 79 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 191 (Polychromatic418967fa.accept_13_12_3_9_1_4341
  77 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 191 (accept_3_2 76
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 191 (accept_3_2 73 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 191 (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 191 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  71 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 191 (accept_3_2 70
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 191 (accept_3_2 67 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 191 (Polychromatic418967fa.accept_15_5_6_11_1_854
  65 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 191 (accept_3_2 64
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 191
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 191 (accept_3_2 61 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 191 (Polychromatic418967fa.accept_13_7_3_9_1_1142
  59 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 191 (accept_3_2 58
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 191
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 191 (accept_3_2 55 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 191 (Polychromatic418967fa.accept_16_5_1_15_1_3922
  53 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 191 (accept_3_2 52
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 191
  (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 191 (accept_3_2 49 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 191 (accept_3_2 46 81
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 191
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 191 (accept_3_2 43 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 191 (accept_3_2 40 81
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 191
  (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 191 (accept_3_2 37 81 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 191 (Polychromatic418967fa.accept_20_16_1_11_1_9647 36 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 191
  (Polychromatic418967fa.accept_15_5_6_11_1_854 35 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 191 (accept_3_2 34 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 191 (accept_3_2 31 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 191
  (Polychromatic418967fa.accept_25_4_6_16_1_11070 29 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 191 (accept_3_2 28 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 191 (accept_3_2 25 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 191
  (Polychromatic418967fa.accept_19_4_5_1_1_4077 23 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 191 (accept_3_2 22 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 191 (accept_3_2 19 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 191
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 191 (accept_3_2 16 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 191 (accept_3_2 13 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 191 (accept_3_2 10 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 191 (accept_3_2 7 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 191 (accept_3_2 4 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 191 (accept_3_2 1 81 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 191 (allA_succ_of_accept 79 80 191 (accept_3_2 79 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 80 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 191 (accept_3_2 76 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 191 (accept_3_2 73 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 191 (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 191 (accept_3_2 70 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 191 (accept_3_2 67 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 191 (Polychromatic418967fa.accept_22_21_14_15_1_3085 65 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 191 (accept_3_2 64 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 191 (accept_3_2 61 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 191 (accept_3_2 58 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 191
  (Polychromatic418967fa.accept_21_14_17_2_1_11069 56 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 80 191 (accept_3_2 55 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 80 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 191 (accept_3_2 52 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 191 (accept_3_2 49 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 191 (accept_3_2 46 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 191
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 191 (accept_3_2 43 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 191 (accept_3_2 40 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 191 (accept_3_2 37 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 191 (Polychromatic418967fa.accept_19_16_4_1_1_5376 35 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 191 (accept_3_2 34 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 191 (accept_3_2 31 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 191 (accept_3_2 28 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 191 (accept_3_2 25 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 191 (accept_3_2 22 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 191 (accept_3_2 19 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 191 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 191 (accept_3_2 16 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 191 (accept_3_2 13 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 191 (accept_3_2 10 80 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 191 (accept_3_2 7 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 191 (accept_3_2 4 80 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  80 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 191 (accept_3_2 1 80 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 191 (allA_of_3_0 79
  79 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 191 (allA_succ_of_accept 77 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 191 (accept_3_2 76 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 74 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 191 (accept_3_2 73 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 191 (Polychromatic418967fa.accept_19_15_2_1_1_2822 72 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 191 (accept_3_2 70 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 191 (accept_3_2 67 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 191 (accept_3_2 64 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 191 (accept_3_2 61 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 191 (Polychromatic418967fa.accept_19_3_2_1_1_11068 60 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 191 (accept_3_2 58 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 191 (Polychromatic418967fa.accept_19_18_2_1_1_5375 56 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 191 (accept_3_2 55 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 191 (Polychromatic418967fa.accept_22_10_12_15_1_11067 54 78
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 191 (accept_3_2 52 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 191 (accept_3_2 49 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 191
  (Polychromatic418967fa.accept_19_9_2_1_1_2821 47 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 191 (accept_3_2 46 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 191 (accept_3_2 43 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 191 (Polychromatic418967fa.accept_16_10_14_15_1_2933 42 78 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 191 (accept_3_2 40 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 191 (accept_3_2 37 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 191 (accept_3_2 34 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 191 (accept_3_2 31 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 191 (accept_3_2 28 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 191 (accept_3_2 25 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 191 (accept_3_2 22 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 191 (accept_3_2 19 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 191 (Polychromatic418967fa.accept_19_18_2_1_1_5375 18 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 191 (accept_3_2 16 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 191 (Polychromatic418967fa.accept_14_1_8_9_1_1312 15 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 191 (accept_3_2 13 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 191
  (Polychromatic418967fa.accept_17_11_10_4_1_5955 11 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 191 (accept_3_2 10 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 191 (accept_3_2 7 78 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 191 (accept_3_2 4 78 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 191
  (Polychromatic418967fa.accept_23_2_9_7_1_11066 2 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 191 (accept_3_2 1 78 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 191
  (allA_succ_of_accept 76 77 191 (accept_3_2 76 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 191 (accept_3_2 73 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 191 (accept_3_2 70 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 191 (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 191 (accept_3_2 67 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 191 (accept_3_2 64 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 191 (Polychromatic418967fa.accept_17_12_9_4_1_5982 63 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 191 (accept_3_2 61 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 191
  (Polychromatic418967fa.accept_21_17_14_2_1_4762 59 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 191 (accept_3_2 58 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 191 (accept_3_2 55 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 191 (accept_3_2 52 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 191 (accept_3_2 49 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 191
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 191 (accept_3_2 46 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 191 (Polychromatic418967fa.accept_20_5_17_11_1_6571 45 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 191 (accept_3_2 43 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 191
  (Polychromatic418967fa.accept_20_1_17_11_1_8119 41 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 191 (accept_3_2 40 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 191 (accept_3_2 37 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 191 (accept_3_2 34 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 191 (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 191 (accept_3_2 31 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 191
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 191 (accept_3_2 28 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 191 (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 191 (accept_3_2 25 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 191
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 191 (accept_3_2 22 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 191 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 191 (accept_3_2 19 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 191 (accept_3_2 16 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 191 (accept_3_2 13 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 191
  (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 191 (accept_3_2 10 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 191 (accept_3_2 7 77 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 191
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 191 (accept_3_2 4 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 191 (accept_3_2 1 77 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 191 (allA_of_3_0 76 76 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 191 (allA_succ_of_accept 74 75
  191 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 191 (accept_3_2 73 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 191 (Polychromatic418967fa.accept_21_9_12_2_1_4781 72 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 191 (accept_3_2 70 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 191 (accept_3_2 67 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 191 (Polychromatic418967fa.accept_16_1_11_15_1_498 65 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 191 (accept_3_2 64 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 191 (Polychromatic418967fa.accept_14_7_5_9_1_2911 63 75 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 191 (accept_3_2 61 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 191 (accept_3_2 58 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 191 (accept_3_2 55 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 191 (accept_3_2 52 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 191 (accept_3_2 49 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 191 (Polychromatic418967fa.accept_17_14_7_4_1_3476 48 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 191 (Polychromatic418967fa.accept_22_3_9_15_1_11065 47 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 191 (accept_3_2 46 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 191 (accept_3_2 43 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 191 (accept_3_2 40 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 191 (accept_3_2 37 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 191 (accept_3_2 34 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 191 (accept_3_2 31 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 191 (Polychromatic418967fa.accept_19_11_18_1_1_4048 30 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 191 (accept_3_2 28 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 191 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 191 (accept_3_2 25 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 191 (accept_3_2 22 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 191 (accept_3_2 19 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 191 (accept_3_2 16 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 191 (accept_3_2 13 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 191 (accept_3_2 10 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 191 (accept_3_2 7 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 191 (accept_3_2 4 75 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 191 (accept_3_2 1 75 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 191 (allA_succ_of_accept
  73 74 191 (accept_3_2 73 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 191
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 191 (Polychromatic418967fa.accept_18_17_2_11_1_9749 71 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 191 (accept_3_2 70 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 68
  74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 191 (accept_3_2 67 74
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 191
  (Polychromatic418967fa.accept_19_9_17_1_1_8325 66 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 191 (accept_3_2 64 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 191 (accept_3_2 61 74
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 191
  (Polychromatic418967fa.accept_19_3_17_1_1_781 60 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 191 (Polychromatic418967fa.accept_16_11_10_15_1_6301 59 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 191 (accept_3_2 58 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 191 (Polychromatic418967fa.accept_11_1_8_4_1_717
  56 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 191 (accept_3_2 55
  74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 191 (accept_3_2 52 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 191
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 50 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 191 (accept_3_2 49 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 191 (accept_3_2 46 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 191 (accept_3_2 43 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 191 (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 191 (accept_3_2 40 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 191
  (Polychromatic418967fa.accept_21_17_11_2_1_7953 38 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 191 (accept_3_2 37 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 191 (Polychromatic418967fa.accept_17_2_6_4_1_2431 36 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 191 (accept_3_2 34 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 191 (accept_3_2 31 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 191 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 191 (accept_3_2 28 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 191 (accept_3_2 25 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 191 (Polychromatic418967fa.accept_22_2_8_15_1_11041 24 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 191 (accept_3_2 22 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 191 (accept_3_2 19 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 191 (accept_3_2 16 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 191
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 191 (accept_3_2 13 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 191 (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 74
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 191 (accept_3_2 10 74 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 191 (accept_3_2 7 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 191 (accept_3_2 4 74 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 191 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2
  74 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 191 (accept_3_2 1 74 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 191 (allA_of_3_0 73 73 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 191 (allA_succ_of_accept 71 72 191
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 71 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 191 (accept_3_2 70 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 68 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 191 (accept_3_2 67 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 191
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 65 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 191 (accept_3_2 64 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 191 (Polychromatic418967fa.accept_19_5_15_1_1_4041 62 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 191 (accept_3_2 61 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 72 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 191
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 191 (accept_3_2 58 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 191 (accept_3_2 55 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 191
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 191 (accept_3_2 52 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 191 (Polychromatic418967fa.accept_25_1_22_16_1_11064 51 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 191 (Polychromatic418967fa.accept_13_11_7_9_1_612 50 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 191 (accept_3_2 49 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 191 (Polychromatic418967fa.accept_21_6_9_2_1_9554 48 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 191
  (Polychromatic418967fa.accept_13_8_7_9_1_611 47 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 191 (accept_3_2 46 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 191 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 191 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 191 (accept_3_2 43 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 191 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 72 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 191
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 191 (accept_3_2 40 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 191 (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 191 (accept_3_2 37 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 191
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 191 (accept_3_2 34 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 191 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 191 (accept_3_2 31 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 191 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 191
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 191 (accept_3_2 28 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 191 (Polychromatic418967fa.accept_19_8_15_1_1_3979 27 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 191 (accept_3_2 25 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 191
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 191 (accept_3_2 22 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 191 (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 191 (accept_3_2 19 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 191
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 191 (accept_3_2 16 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 191 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 191 (accept_3_2 13 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 191 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 72
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 191
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 191 (accept_3_2 10 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 191 (accept_3_2 7 72 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 191
  (Polychromatic418967fa.accept_19_5_15_1_1_4041 5 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 191 (accept_3_2 4 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  191 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 72 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 191 (accept_3_2 1 72 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 191
  (allA_succ_of_accept 70 71 191 (accept_3_2 70 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 191 (accept_3_2 67 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 191
  (Polychromatic418967fa.accept_11_10_5_4_1_711 65 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 191 (accept_3_2 64 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 63 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 191 (accept_3_2 61 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 191 (accept_3_2 58 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 191 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 191 (accept_3_2 55 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 191
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 191 (accept_3_2 52 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 191 (accept_3_2 49 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 191
  (Polychromatic418967fa.accept_17_13_3_4_1_2537 47 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 191 (accept_3_2 46 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 191 (Polychromatic418967fa.accept_19_6_14_1_1_2752 44 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 191 (accept_3_2 43 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 191 (accept_3_2 40 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 191 (accept_3_2 37 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 191 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 191
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 191 (accept_3_2 34 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 191 (accept_3_2 31 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 191
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 191 (accept_3_2 28 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 191 (Polychromatic418967fa.accept_21_5_8_2_1_11063 26 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 191 (accept_3_2 25 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 191 (accept_3_2 22 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 191 (accept_3_2 19 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 191 (Polychromatic418967fa.accept_19_18_14_1_1_8323 18 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 191 (accept_3_2 16 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 191 (accept_3_2 13 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 191
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 191 (accept_3_2 10 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 191 (Polychromatic418967fa.accept_19_9_14_1_1_6792 9 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 191 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 191 (accept_3_2 7 71 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 191 (accept_3_2 4 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 71 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 191 (accept_3_2 1 71 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 191
  (allA_of_3_0 70 70 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 191 (allA_succ_of_accept 68 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 191 (accept_3_2 67 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 191 (accept_3_2 64 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 191 (accept_3_2 61 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 191 (accept_3_2 58 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 191 (accept_3_2 55 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 191 (accept_3_2 52 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 191 (accept_3_2 49 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 191 (Polychromatic418967fa.accept_13_8_4_9_1_1145 47 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 191 (accept_3_2 46 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 191 (accept_3_2 43 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 191 (accept_3_2 40 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 191 (accept_3_2 37 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 191 (accept_3_2 34 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 191 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 191 (accept_3_2 31 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 191 (accept_3_2 28 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 191 (accept_3_2 25 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 191 (accept_3_2 22 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 191 (accept_3_2 19 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 191 (accept_3_2 16 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 191 (accept_3_2 13 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 191 (accept_3_2 10 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 191 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 69 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 191 (accept_3_2 7 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 69 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 191 (accept_3_2 4 69 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 191 (accept_3_2 1 69 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 191 (allA_succ_of_accept 67 68
  191 (accept_3_2 67 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 191 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 191 (accept_3_2 64 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 62
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 191 (accept_3_2 61 68
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 191 (accept_3_2 58 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 191 (Polychromatic418967fa.accept_16_8_4_15_1_2941
  56 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 191 (accept_3_2 55
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 191
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 191 (accept_3_2 52 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  50 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 191 (accept_3_2 49
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 191 (accept_3_2 46 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 191 (accept_3_2 43 68
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 191
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 191 (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 191 (accept_3_2 40 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 191 (accept_3_2 37 68
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 191
  (Polychromatic418967fa.accept_24_12_20_23_1_11062 36 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 191 (accept_3_2 34 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 191 (accept_3_2 31 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 191 (accept_3_2 28 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 191 (accept_3_2 25 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 191 (accept_3_2 22 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 191
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 191 (accept_3_2 19 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 191 (accept_3_2 16 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 191 (accept_3_2 13 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 191 (accept_3_2 10 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 191 (accept_3_2 7 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 191 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 191 (accept_3_2 4 68 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  68 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 191 (accept_3_2 1 68 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 191 (allA_of_3_0 67 67 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 191 (allA_succ_of_accept 65 66 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 191 (accept_3_2 64 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 191 (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 191 (accept_3_2 61 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 191 (accept_3_2 58 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 191 (Polychromatic418967fa.accept_20_16_6_11_1_9657 56 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 191 (accept_3_2 55 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 66 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 191 (accept_3_2 52 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 191 (accept_3_2 49 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 191 (accept_3_2 46 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 191 (accept_3_2 43 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 191 (accept_3_2 40 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 191 (Polychromatic418967fa.accept_21_17_3_2_1_2111 38 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 191 (accept_3_2 37 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 191 (accept_3_2 34 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 191 (accept_3_2 31 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 191 (Polychromatic418967fa.accept_19_11_9_1_1_2809 30 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 191 (accept_3_2 28 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 191 (accept_3_2 25 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 191 (accept_3_2 22 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 191 (accept_3_2 19 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 191 (accept_3_2 16 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 191 (accept_3_2 13 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 191
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 191 (accept_3_2 10 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 191 (accept_3_2 7 66 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 191 (accept_3_2 4 66 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 3
  66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 191 (accept_3_2 1 66 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 191 (allA_succ_of_accept 64 65 191
  (accept_3_2 64 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 191
  (Polychromatic418967fa.accept_27_9_11_2_1_414 63 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 191 (accept_3_2 61 65 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 191 (accept_3_2 58 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 191 (Polychromatic418967fa.accept_20_17_5_11_1_9622 57 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 191 (accept_3_2 55 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 191
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 191 (accept_3_2 52 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 191 (Polychromatic418967fa.accept_15_6_5_11_1_2378 51 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 191 (accept_3_2 49 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 191 (Polychromatic418967fa.accept_22_4_21_15_1_11061 48 65 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 191 (accept_3_2 46 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 191 (Polychromatic418967fa.accept_19_7_8_1_1_4028 45 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 191 (accept_3_2 43 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 191
  (Polychromatic418967fa.accept_17_7_14_4_1_4745 41 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 191 (accept_3_2 40 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 191 (accept_3_2 37 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 191
  (Polychromatic418967fa.accept_17_1_14_4_1_1550 35 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 191 (accept_3_2 34 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 191 (Polychromatic418967fa.accept_22_11_21_15_1_7853 33 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 191 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 191 (accept_3_2 31 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 191 (accept_3_2 28 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 191 (accept_3_2 25 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 191
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 191 (accept_3_2 22 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 191 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 191 (Polychromatic418967fa.accept_22_20_21_15_1_11060 20 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 191 (accept_3_2 19 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 191 (accept_3_2 16 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 191 (Polychromatic418967fa.accept_19_15_8_1_1_6794 15 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 191 (accept_3_2 13 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 191 (Polychromatic418967fa.accept_19_12_8_1_1_11059 12 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 191 (accept_3_2 10 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 191 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 191 (accept_3_2 7 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 191
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 191 (accept_3_2 4 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  191 (Polychromatic418967fa.accept_23_3_19_7_1_7717 3 65 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 65 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 191 (accept_3_2 1 65 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 65 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64
  191 (allA_of_3_0 64 64 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 191 (allA_succ_of_accept 62 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 191 (accept_3_2 61 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 191 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 191 (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 191 (accept_3_2 58 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 191 (accept_3_2 55 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 191 (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 191 (accept_3_2 52 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 191 (accept_3_2 49 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 191 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 191 (accept_3_2 46 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 191 (accept_3_2 43 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 41 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 191 (accept_3_2 40 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 191 (Polychromatic418967fa.accept_27_12_9_2_1_11058 39 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 191 (accept_3_2 37 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 191 (Polychromatic418967fa.accept_23_12_17_7_1_4310 35 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 191 (accept_3_2 34 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 191 (accept_3_2 31 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 191 (accept_3_2 28 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 191 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 191 (accept_3_2 25 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 191 (Polychromatic418967fa.accept_17_7_12_4_1_2524 24 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 191 (accept_3_2 22 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 191 (accept_3_2 19 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 191 (Polychromatic418967fa.accept_27_17_9_2_1_11057 17 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 191 (accept_3_2 16 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 63 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 191 (accept_3_2 13 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 191 (Polychromatic418967fa.accept_19_11_6_1_1_2826 11 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 191 (accept_3_2 10 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 191 (accept_3_2 7 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  191 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 191 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 191 (accept_3_2 4 63 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 191 (Polychromatic418967fa.accept_19_3_6_1_1_4064 3 63 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 191 (accept_3_2 1 63 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 191 (allA_succ_of_accept 61 62 191
  (accept_3_2 61 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 191 (accept_3_2 58 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 191 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 191 (accept_3_2 55
  62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 191
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 191 (accept_3_2 52 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 191 (accept_3_2 49 62
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 191 (accept_3_2 46 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 191 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 191 (accept_3_2 43
  62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 191
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 191 (accept_3_2 40 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 191 (accept_3_2 37 62
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 191 (Polychromatic418967fa.accept_7_1_6_2_1_18
  36 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 191 (accept_3_2 34 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 191 (accept_3_2 31 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 62 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 191 (accept_3_2 28 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 191 (accept_3_2 25 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 191 (accept_3_2 22 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 191 (accept_3_2 19 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 191 (accept_3_2 16 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 191 (accept_3_2 13 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 62 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 191 (accept_3_2 10 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 191 (accept_3_2 7 62 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 191 (accept_3_2 4 62 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 191
  (Polychromatic418967fa.accept_25_2_12_16_1_11056 2 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 191 (accept_3_2 1 62 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 191 (allA_of_3_0 61 61 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 191 (allA_succ_of_accept 59 60 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 191 (accept_3_2 58 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 191 (Polychromatic418967fa.accept_13_4_8_9_1_1156 56 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 191 (accept_3_2 55 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 191 (accept_3_2 52 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 191 (accept_3_2 49 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 191 (accept_3_2 46 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 191 (Polychromatic418967fa.accept_16_13_12_15_1_6290 45 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 191 (accept_3_2 43 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 191 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 191 (accept_3_2 40 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 191 (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 191 (accept_3_2 37 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 191 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 60
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 191 (accept_3_2 34 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 191 (accept_3_2 31 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 191
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 191 (accept_3_2 28 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 191 (accept_3_2 25 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 191 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 191 (accept_3_2 22 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 191 (accept_3_2 19 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 191 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 191 (accept_3_2 16 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 191 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 191 (accept_3_2 13 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 191 (accept_3_2 10 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 191 (Polychromatic418967fa.accept_22_9_16_15_1_11055 9 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 191 (accept_3_2 7 60 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 191 (accept_3_2 4 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  191 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 191 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 60 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 191 (accept_3_2 1 60 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 191
  (allA_succ_of_accept 58 59 191 (accept_3_2 58 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 191 (Polychromatic418967fa.accept_13_4_7_9_1_5260 56 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 191 (accept_3_2 55 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 191 (accept_3_2 52 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 191 (accept_3_2 49 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 191 (accept_3_2 46 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 191 (accept_3_2 43 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 191 (accept_3_2 40 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 191 (accept_3_2 37 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 191 (accept_3_2 34 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 191 (accept_3_2 31 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 191 (accept_3_2 28 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 191 (accept_3_2 25 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 191
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 191 (accept_3_2 22 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 191 (accept_3_2 19 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 191 (accept_3_2 16 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 191 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 191 (accept_3_2 13 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 191
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 191 (accept_3_2 10 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 191 (Polychromatic418967fa.accept_19_9_2_1_1_2821 9 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 191 (accept_3_2 7 59 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 191 (accept_3_2 4 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 59 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 191 (accept_3_2 1 59 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 191 (allA_of_3_0
  58 58 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 191 (allA_succ_of_accept 56 57 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 191 (accept_3_2 55 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 191 (accept_3_2 52 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 191 (accept_3_2 49 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 191 (Polychromatic418967fa.accept_25_22_7_16_1_11054 47 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 191 (accept_3_2 46 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 191 (accept_3_2 43 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 191 (accept_3_2 40 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 191 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 191 (accept_3_2 37 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 191 (accept_3_2 34 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 191 (accept_3_2 31 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 191 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 191 (accept_3_2 28 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 191 (accept_3_2 25 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 191 (accept_3_2 22 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 191 (Polychromatic418967fa.accept_20_1_17_11_1_8119 21 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 191 (accept_3_2 19 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 191 (accept_3_2 16 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 191 (accept_3_2 13 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 191 (Polychromatic418967fa.accept_24_12_9_23_1_7477 12 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 191 (Polychromatic418967fa.accept_17_11_6_4_1_4729 11 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 191 (accept_3_2 10 57 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 57 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 191 (accept_3_2 7 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 57 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 191 (accept_3_2 4 57 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 191 (accept_3_2 1 57 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 191)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 191 (allA_succ_of_accept 55 56 191 (accept_3_2 55 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 191 (Polychromatic418967fa.accept_21_12_14_2_1_11053 54 56 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 191 (Polychromatic418967fa.accept_18_17_2_11_1_9749 53 56
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 191 (accept_3_2 52 56 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 191 (accept_3_2 49 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 191 (Polychromatic418967fa.accept_21_6_14_2_1_7980 48 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 191 (accept_3_2 46 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 191
  (Polychromatic418967fa.accept_13_5_4_9_1_601 44 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 191 (accept_3_2 43 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 191 (accept_3_2 40 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 191 (accept_3_2 37 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 191 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 191 (accept_3_2 34 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 191 (accept_3_2 31 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 191 (Polychromatic418967fa.accept_21_8_14_2_1_7981 29 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 191 (accept_3_2 28 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 191 (accept_3_2 25 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 191 (Polychromatic418967fa.accept_19_5_18_1_1_11052 24 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 191 (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 191 (accept_3_2 22 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 191
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 191 (accept_3_2 19 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 191 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 191 (accept_3_2 16 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 191 (accept_3_2 13 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 191 (Polychromatic418967fa.accept_19_11_18_1_1_4048 11 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 191 (accept_3_2 10 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 191
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 191 (accept_3_2 7 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  191 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 191 (accept_3_2 4 56 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 191 (accept_3_2 1 56 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 191 (allA_of_3_0 55 55 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 191 (allA_succ_of_accept 53 54 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 191 (accept_3_2 52 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 191 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 50 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 191 (accept_3_2 49 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 191 (Polychromatic418967fa.accept_19_10_16_1_1_8271 48 54
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 191
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 191 (accept_3_2 46 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 191 (accept_3_2 43 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 191 (accept_3_2 40 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 191 (accept_3_2 37 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 191 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 191
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 191 (accept_3_2 34 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 191 (accept_3_2 31 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 191 (Polychromatic418967fa.accept_17_13_3_4_1_2537 30 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 191 (accept_3_2 28 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 191 (Polychromatic418967fa.accept_20_6_14_11_1_6537 26 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 191 (accept_3_2 25 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 191
  (Polychromatic418967fa.accept_16_7_6_15_1_495 23 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 191 (accept_3_2 22 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 191 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 191 (accept_3_2 19 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 191 (accept_3_2 16 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 191 (accept_3_2 13 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 191 (Polychromatic418967fa.accept_22_12_10_15_1_4511 12 54 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 191 (accept_3_2 10 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 54 191 (Polychromatic418967fa.accept_19_8_16_1_1_11051 8 54 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 191 (accept_3_2 7 54 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 54 191 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 54 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 191 (accept_3_2 4 54 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 191
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 191 (accept_3_2 1 54 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  191)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 191 (allA_succ_of_accept 52 53 191 (accept_3_2
  52 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 191
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 191 (accept_3_2 49 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 191 (accept_3_2 46 53
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 191
  (Polychromatic418967fa.accept_13_6_1_9_1_619 45 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 44 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 191 (accept_3_2 43 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 191 (accept_3_2 40 53
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 191 (accept_3_2 37 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 191 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 191
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 191 (accept_3_2 34 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 191 (accept_3_2 31 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 191
  (Polychromatic418967fa.accept_17_12_2_4_1_11050 29 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 191 (accept_3_2 28 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 191 (accept_3_2 25 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 191 (accept_3_2 22 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 191 (accept_3_2 19 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 191
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 191 (accept_3_2 16 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 191 (accept_3_2 13 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 191
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 191 (accept_3_2 10 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 191 (Polychromatic418967fa.accept_17_9_2_4_1_3472 9 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 191 (accept_3_2 7 53 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 191 (accept_3_2 4 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 191 (accept_3_2 1 53 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 191))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 191 (allA_of_3_0 52 52
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 191 (allA_succ_of_accept 50 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 191 (accept_3_2 49 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 191 (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 191 (accept_3_2 46 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 191 (accept_3_2 43 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 191 (Polychromatic418967fa.accept_13_3_12_9_1_1193 42 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 191 (accept_3_2 40 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 191 (accept_3_2 37 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 191 (accept_3_2 34 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 191 (accept_3_2 31 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 191 (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 191 (accept_3_2 28 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 51
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 191 (accept_3_2 25 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 191 (accept_3_2 22 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 191 (accept_3_2 19 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 191 (accept_3_2 16 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 191 (Polychromatic418967fa.accept_21_15_9_2_1_7973 15 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 191 (accept_3_2 13 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 191 (accept_3_2 10 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 191 (accept_3_2 7 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  191 (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 51 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 191 (accept_3_2 4 51 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 191 (accept_3_2 1 51 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  191))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 191 (allA_succ_of_accept 49 50 191 (accept_3_2 49
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 191 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 191 (accept_3_2 46 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 191 (accept_3_2 43 50
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 191
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 191 (accept_3_2 40 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 191 (accept_3_2 37 50
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 191
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 191 (accept_3_2 34 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 191 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 191 (accept_3_2 31
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 191 (accept_3_2 28 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 191 (accept_3_2 25 50
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 191 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 191 (accept_3_2 22 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 191 (accept_3_2 19 50
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 191
  (Polychromatic418967fa.accept_19_18_12_1_1_9737 18 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 191 (accept_3_2 16 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 191 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  14 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 191 (accept_3_2 13
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 191 (Polychromatic418967fa.accept_19_11_12_1_1_11049 11 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 191 (accept_3_2 10 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 191 (accept_3_2 7 50 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 191 (accept_3_2 4 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50
  191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 191 (accept_3_2 1 50 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 191)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 191 (allA_of_3_0 49 49
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 191 (allA_succ_of_accept 47 48 191
  (Polychromatic418967fa.accept_17_13_14_4_1_2468 47 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 191 (accept_3_2 46 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 191 (accept_3_2 43 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 191 (accept_3_2 40 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 191 (accept_3_2 37 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 191 (accept_3_2 34 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 191 (accept_3_2 31 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 191 (Polychromatic418967fa.accept_17_13_14_4_1_2468 30 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 191 (accept_3_2 28 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 191 (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 191 (accept_3_2 25 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 191 (accept_3_2 22 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 191 (Polychromatic418967fa.accept_21_20_6_2_1_11048 20 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 191 (accept_3_2 19 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 191 (accept_3_2 16 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 191 (accept_3_2 13 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 191 (Polychromatic418967fa.accept_21_12_6_2_1_7950 12 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 191 (accept_3_2 10 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 191 (accept_3_2 7 48 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 191 (accept_3_2 4 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 191 (Polychromatic418967fa.accept_25_2_23_16_1_11047 2 48 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 191 (accept_3_2 1 48 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 191)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 191 (allA_succ_of_accept 46
  47 191 (accept_3_2 46 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 191 (accept_3_2 43 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 191 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 191 (Polychromatic418967fa.accept_20_1_7_11_1_3673
  41 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 191 (accept_3_2 40
  47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 191 (accept_3_2 37 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 191 (Polychromatic418967fa.accept_14_7_5_9_1_2911
  35 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 191 (accept_3_2 34
  47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 191
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 191 (accept_3_2 31 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 191 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 191 (Polychromatic418967fa.accept_11_7_3_4_1_729
  29 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 191 (accept_3_2 28
  47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 191
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 191 (accept_3_2 25 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 191
  (Polychromatic418967fa.accept_22_1_3_15_1_11046 23 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 191 (accept_3_2 22 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 191 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 191 (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 191 (accept_3_2 19 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 191 (accept_3_2 16 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 191 (Polychromatic418967fa.accept_25_15_22_16_1_11045 15 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 191 (accept_3_2 13 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 191 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 47 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 191 (accept_3_2 10 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 191 (Polychromatic418967fa.accept_17_8_13_4_1_6012 8 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 191 (accept_3_2 7 47 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 47 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 191 (accept_3_2 4 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 191 (Polychromatic418967fa.accept_19_2_9_1_1_4029 2 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 191 (accept_3_2 1 47 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 191))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 191 (allA_of_3_0 46 46 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 191 (allA_succ_of_accept 44 45 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 191 (accept_3_2 43 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 191 (accept_3_2 40 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 191 (accept_3_2 37 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 191 (Polychromatic418967fa.accept_16_3_13_15_1_1913 35 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 191 (accept_3_2 34 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 191 (accept_3_2 31 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 191 (accept_3_2 28 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 191 (accept_3_2 25 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 191 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 191 (accept_3_2 22 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 191 (Polychromatic418967fa.accept_19_2_7_1_1_2808 21 45 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 191 (accept_3_2 19 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 191 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 191 (accept_3_2 16 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 191 (accept_3_2 13 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 191 (Polychromatic418967fa.accept_22_11_1_15_1_11044 11 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 191 (accept_3_2 10 45 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 191 (accept_3_2 7 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 191 (accept_3_2 4 45 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 191 (accept_3_2 1 45 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 191))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  191 (allA_succ_of_accept 43 44 191 (accept_3_2 43 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 191 (accept_3_2 40 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 191 (accept_3_2 37 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 191 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 191 (accept_3_2 34 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 191 (accept_3_2 31 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 191 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 191 (accept_3_2 28 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 191 (accept_3_2 25 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 191 (accept_3_2 22 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 191
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 20 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 191 (accept_3_2 19 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 191 (accept_3_2 16 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 191 (accept_3_2 13 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 191 (accept_3_2 10 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 191
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 191 (accept_3_2 7 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 191 (accept_3_2 4 44 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  44 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 191 (accept_3_2 1 44 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 191)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  191 (allA_of_3_0 43 43 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 191 (allA_succ_of_accept 41 42 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 191 (accept_3_2 40 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 191 (Polychromatic418967fa.accept_13_12_3_9_1_4341 38 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 191 (accept_3_2 37 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 191 (accept_3_2 34 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 191 (accept_3_2 31 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 191 (accept_3_2 28 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 191 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 191 (accept_3_2 25 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 191 (accept_3_2 22 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 191 (Polychromatic418967fa.accept_13_7_3_9_1_1142 20 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 191 (accept_3_2 19 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 191 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 191 (accept_3_2 16 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 191 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 191 (accept_3_2 13 42 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 191
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 42 191 (accept_3_2 10 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 42 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 191 (accept_3_2 7 42 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 191 (accept_3_2 4 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 42 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 191 (accept_3_2 1 42 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 191)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 191 (allA_succ_of_accept 40 41
  191 (accept_3_2 40 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 191 (accept_3_2 37 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 191 (accept_3_2 34 41
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 191
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 191 (accept_3_2 31 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 191 (accept_3_2 28 41
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 191
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 191 (accept_3_2 25 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 191 (Polychromatic418967fa.accept_11_1_8_4_1_717
  23 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 191 (accept_3_2 22
  41 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 191 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 191 (accept_3_2 19 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 191 (accept_3_2 16 41
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 191 (Polychromatic418967fa.accept_7_1_6_2_1_18
  15 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 191 (accept_3_2 13 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 191 (accept_3_2 10 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 191 (Polychromatic418967fa.accept_21_9_20_2_1_8000 9 41 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 191
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 191 (accept_3_2 7 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 191 (accept_3_2 4 41 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 191 (accept_3_2 1 41 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 191))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 191
  (allA_of_3_0 40 40 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 191 (allA_succ_of_accept 38 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 191 (accept_3_2 37 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 191 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 191 (accept_3_2 34 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 191 (accept_3_2 31 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 191 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 191 (Polychromatic418967fa.accept_24_5_15_23_1_5647 29 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 191 (accept_3_2 28 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 191 (accept_3_2 25 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 191 (accept_3_2 22 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 191 (accept_3_2 19 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 191 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 191 (accept_3_2 16 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 191 (accept_3_2 13 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 191 (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 191 (accept_3_2 10 39 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 191 (accept_3_2 7 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 191 (accept_3_2 4 39 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 191 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 39 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 191 (accept_3_2 1 39 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 191))))))))))))))))))))))))))))))))))))))) (allB_succ 38 191
  (allA_succ_of_accept 37 38 191 (accept_3_2 37 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 191 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 191 (accept_3_2 34 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 191
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 191 (accept_3_2 31 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 191 (Polychromatic418967fa.accept_21_9_17_2_1_9537 30 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 191 (accept_3_2 28 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 191 (accept_3_2 25 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 191 (Polychromatic418967fa.accept_21_3_17_2_1_11043 24 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 191 (accept_3_2 22 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 191 (accept_3_2 19 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 191 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 191 (accept_3_2 16 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 191
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 191 (accept_3_2 13 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 191 (Polychromatic418967fa.accept_21_11_17_2_1_4749 11 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 191 (accept_3_2 10 38 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 191 (accept_3_2 7 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 191 (accept_3_2 4 38 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 191 (Polychromatic418967fa.accept_23_2_15_7_1_11042
  2 38 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 191 (accept_3_2 1 38
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 191)))))))))))))))))))))))))))))))))))))) (allB_succ 37 191
  (allA_of_3_0 37 37 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 191 (allA_succ_of_accept 35 36 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 191 (accept_3_2 34 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 191 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 191 (accept_3_2 31 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 191 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 36 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 191
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 191 (accept_3_2 28 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 191 (Polychromatic418967fa.accept_17_9_2_4_1_3472 26 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 191 (accept_3_2 25 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 191
  (Polychromatic418967fa.accept_17_6_2_4_1_2421 23 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 191 (accept_3_2 22 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 191 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 191 (accept_3_2 19 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 36 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 191 (accept_3_2 16 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 191 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 191 (accept_3_2 13 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 191
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 191 (accept_3_2 10 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 191 (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 191 (accept_3_2 7 36 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 191
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 191 (accept_3_2 4 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 191 (accept_3_2 1 36 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 191)))))))))))))))))))))))))))))))))))) (allB_succ 35 191 (allA_succ_of_accept 34 35 191
  (accept_3_2 34 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 191
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 191 (accept_3_2 31 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  29 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 191 (accept_3_2 28
  35 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 191
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 191 (accept_3_2 25 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 191 (accept_3_2 22 35
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 191 (accept_3_2 19 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 191 (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 35 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 191
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 191 (accept_3_2 16 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 191 (accept_3_2 13 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 191
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 191 (accept_3_2 10 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 191 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 191 (accept_3_2 7 35 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 191 (accept_3_2 4 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 35 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 2 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 191 (accept_3_2 1 35 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 191))))))))))))))))))))))))))))))))))) (allB_succ 34 191 (allA_of_3_0 34 34 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 191 (allA_succ_of_accept 32 33 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 191 (accept_3_2 31 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 191 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 191 (accept_3_2 28 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 191 (accept_3_2 25 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 191 (accept_3_2 22 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 191 (accept_3_2 19 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 191 (accept_3_2 16 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 33 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 191 (accept_3_2 13 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 191 (accept_3_2 10 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 191 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 33 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 191 (accept_3_2 7 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 191 (accept_3_2 4 33 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 191 (accept_3_2 1 33 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 191))))))))))))))))))))))))))))))))) (allB_succ 32 191
  (allA_succ_of_accept 31 32 191 (accept_3_2 31 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 191 (accept_3_2 28 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 191 (accept_3_2 25 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 191 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 191 (accept_3_2 22 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 191 (accept_3_2 19 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 191 (Polychromatic418967fa.accept_19_18_13_1_1_9735 18 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 191 (accept_3_2 16 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 191 (accept_3_2 13 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 191 (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 32 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 191 (accept_3_2 10 32 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 191 (accept_3_2 7 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 191 (accept_3_2 4 32 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  32 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 191 (accept_3_2 1 32 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 191)))))))))))))))))))))))))))))))) (allB_succ 31 191
  (allA_of_3_0 31 31 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 191 (allA_succ_of_accept 29 30 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 191 (accept_3_2 28 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 191 (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 191 (accept_3_2 25 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 30 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 191 (accept_3_2 22 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 191 (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 191 (accept_3_2 19 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 30 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 191 (accept_3_2 16 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 191 (accept_3_2 13 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 30 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 191
  (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 191 (accept_3_2 10 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 191 (accept_3_2 7 30 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 30 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 191 (accept_3_2 4 30 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 191 (Polychromatic418967fa.accept_17_3_13_4_1_8530
  3 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 191
  (Polychromatic418967fa.accept_22_2_8_15_1_11041 2 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 191 (accept_3_2 1 30 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  191)))))))))))))))))))))))))))))) (allB_succ 29 191 (allA_succ_of_accept 28 29 191 (accept_3_2 28 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 191 (accept_3_2 25 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 191 (Polychromatic418967fa.accept_19_4_10_1_1_2776 23 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 191 (accept_3_2 22 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 191 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 29 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 191 (accept_3_2 19 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 191 (accept_3_2 16 29 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 191 (accept_3_2 13 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 191 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 191 (Polychromatic418967fa.accept_19_11_10_1_1_2773 11 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 191 (accept_3_2 10 29 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 191 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 29 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 191
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 191 (accept_3_2 7 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 29 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 191 (accept_3_2 4 29 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 191 (accept_3_2 1 29 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 191))))))))))))))))))))))))))))) (allB_succ 28 191 (allA_of_3_0
  28 28 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 191 (allA_succ_of_accept 26 27 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 191 (accept_3_2 25 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 191 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 27 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 191 (accept_3_2 22 27 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 191 (accept_3_2 19 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 191 (accept_3_2 16 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 191 (accept_3_2 13 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 191 (accept_3_2 10 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 191 (accept_3_2 7 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 191 (accept_3_2 4 27 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 191 (accept_3_2 1 27 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  191))))))))))))))))))))))))))) (allB_succ 26 191 (allA_succ_of_accept 25 26 191 (accept_3_2 25 26 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 191 (accept_3_2 22 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 191 (accept_3_2 19 26 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 191 (accept_3_2 16 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 191 (accept_3_2 13 26 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 191 (accept_3_2 10 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 26 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 191 (accept_3_2 7 26 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 26 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 191 (accept_3_2 4 26 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 191 (accept_3_2 1 26 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  191)))))))))))))))))))))))))) (allB_succ 25 191 (allA_of_3_0 25 25 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 191 (allA_succ_of_accept 23 24 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 191 (accept_3_2 22 24 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 191 (accept_3_2 19 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 191 (Polychromatic418967fa.accept_19_18_5_1_1_8255 18 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 191 (accept_3_2 16 24 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 191 (accept_3_2 13 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 191 (Polychromatic418967fa.accept_25_11_24_16_1_7288 11 24 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 191 (accept_3_2 10 24 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 24 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 191 (accept_3_2 7 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 191 (accept_3_2 4 24 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 2
  24 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 191 (accept_3_2 1 24 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 191)))))))))))))))))))))))) (allB_succ 23 191
  (allA_succ_of_accept 22 23 191 (accept_3_2 22 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  23 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 191 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 23 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 191 (accept_3_2 19 23 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 23 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 191 (accept_3_2 16 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 191 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 23 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 191 (accept_3_2 13 23 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 191
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 191 (accept_3_2 10 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 191 (Polychromatic418967fa.accept_22_9_1_15_1_9461 9 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 191 (accept_3_2 7 23 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 191 (accept_3_2 4 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 23 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 191 (accept_3_2 1 23 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 191))))))))))))))))))))))) (allB_succ 22 191 (allA_of_3_0 22 22 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 191 (allA_succ_of_accept 20 21 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 191 (accept_3_2 19 21 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 191 (accept_3_2 16 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 191 (accept_3_2 13 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 191 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 21 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 191 (accept_3_2 10 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 191 (accept_3_2 7 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 191 (accept_3_2 4 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 191 (accept_3_2 1 21 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 191))))))))))))))))))))) (allB_succ 20 191 (allA_succ_of_accept 19 20 191
  (accept_3_2 19 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 191 (accept_3_2 16 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 191 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 191 (accept_3_2 13
  20 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 191
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 191 (accept_3_2 10 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 191 (accept_3_2 7 20 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 191 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6
  20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 191
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 191 (accept_3_2 4 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 191 (accept_3_2 1 20 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 191)))))))))))))))))))) (allB_succ 19 191 (allA_of_3_0 19 19 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 191 (allA_succ_of_accept 17 18 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 191 (accept_3_2 16 18 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 191 (Polychromatic418967fa.accept_13_2_5_9_1_610
  15 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 191
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 191 (accept_3_2 13 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 191 (Polychromatic418967fa.accept_19_11_18_1_1_4048 11 18 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 191 (accept_3_2 10 18 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 191
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 191 (accept_3_2 7 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 191 (accept_3_2 4 18 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 18 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 191 (Polychromatic418967fa.accept_13_2_5_9_1_610 2
  18 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 191 (accept_3_2 1 18 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 191)))))))))))))))))) (allB_succ 17 191 (allA_succ_of_accept 16
  17 191 (accept_3_2 16 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 191 (accept_3_2 13 17 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 191 (accept_3_2 10 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 191 (accept_3_2 7 17 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 191 (accept_3_2 4 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 191 (accept_3_2 1 17 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 191))))))))))))))))) (allB_succ 16 191 (allA_of_3_0 16 16 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 191 (allA_succ_of_accept 14 15 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 191 (accept_3_2 13 15 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12
  15 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 191
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 191 (accept_3_2 10 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 191 (accept_3_2 7 15 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 191 (accept_3_2 4 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 191 (accept_3_2 1 15 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 191))))))))))))))) (allB_succ 14 191 (allA_succ_of_accept 13 14 191 (accept_3_2 13 14 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12
  14 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 191
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 14 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 191 (accept_3_2 10 14 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 191 (accept_3_2 7 14 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 191 (accept_3_2 4 14 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 191
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 14 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 191 (accept_3_2 1 14 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  191)))))))))))))) (allB_succ 13 191 (allA_of_3_0 13 13 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 191
  (allA_succ_of_accept 11 12 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 191 (accept_3_2 10 12 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 191 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  12 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 191 (accept_3_2 7 12 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  12 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 191 (accept_3_2 4 12 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 191 (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 12 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 191 (accept_3_2 1 12 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 191)))))))))))) (allB_succ 11 191 (allA_succ_of_accept 10 11 191 (accept_3_2 10 11 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 191 (Polychromatic418967fa.accept_19_9_11_1_1_8239
  9 11 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 191
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 11 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 191 (accept_3_2 7 11 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 11 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 191 (accept_3_2 4 11 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 191 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 11 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 2
  11 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 191 (accept_3_2 1 11 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 191))))))))))) (allB_succ 10 191 (allA_of_3_0 10 10 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 191 (allA_succ_of_accept 8 9 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 191 (accept_3_2 7 9 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 191 (accept_3_2 4 9 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 191 (accept_3_2 1 9 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 191))))))))) (allB_succ 8 191 (allA_succ_of_accept 7 8 191
  (accept_3_2 7 8 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 191 (accept_3_2 4 8 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 191 (accept_3_2 1 8 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 191)))))))) (allB_succ 7 191 (allA_of_3_0 7 7 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 191 (allA_succ_of_accept 5 6 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 191 (accept_3_2 4 6 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 6 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 191 (accept_3_2 1 6 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 191)))))) (allB_succ 5 191 (allA_succ_of_accept 4 5 191 (accept_3_2 4 5 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 191 (accept_3_2 1 5 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 191)))))
  (allB_succ 4 191 (allA_of_3_0 4 4 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 191 (allA_succ_of_accept 2
  3 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 191 (accept_3_2 1 3 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 191)))
  (allB_succ 2 191 (allA_succ_of_accept 1 2 191 (accept_3_2 1 2 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  191)) (allB_two
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


